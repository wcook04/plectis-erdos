import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyThreeFEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyThreeFEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyThreeFEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyThreeFEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyThreeFEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyThreeFEFastPow a n * oneHundredSixtyThreeFEFastPow a n * a else oneHundredSixtyThreeFEFastPow a n * oneHundredSixtyThreeFEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyThreeFE_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1453 : Nat.Prime 1453 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1601 : Nat.Prime 1601 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1657 : Nat.Prime 1657 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1747 : Nat.Prime 1747 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2161 : Nat.Prime 2161 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2729 : Nat.Prime 2729 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2963 : Nat.Prime 2963 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3137 : Nat.Prime 3137 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3307 : Nat.Prime 3307 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3527 : Nat.Prime 3527 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4001 : Nat.Prime 4001 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4129 : Nat.Prime 4129 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4639 : Nat.Prime 4639 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4651 : Nat.Prime 4651 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4721 : Nat.Prime 4721 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4817 : Nat.Prime 4817 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5113 : Nat.Prime 5113 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5987 : Nat.Prime 5987 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6073 : Nat.Prime 6073 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6221 : Nat.Prime 6221 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6379 : Nat.Prime 6379 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6389 : Nat.Prime 6389 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6491 : Nat.Prime 6491 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6569 : Nat.Prime 6569 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6793 : Nat.Prime 6793 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7079 : Nat.Prime 7079 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7307 : Nat.Prime 7307 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7351 : Nat.Prime 7351 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7433 : Nat.Prime 7433 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8147 : Nat.Prime 8147 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8537 : Nat.Prime 8537 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8599 : Nat.Prime 8599 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8821 : Nat.Prime 8821 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8929 : Nat.Prime 8929 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_9007 : Nat.Prime 9007 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11071 : Nat.Prime 11071 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11887 : Nat.Prime 11887 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12281 : Nat.Prime 12281 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12343 : Nat.Prime 12343 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12457 : Nat.Prime 12457 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12497 : Nat.Prime 12497 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12697 : Nat.Prime 12697 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12979 : Nat.Prime 12979 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13127 : Nat.Prime 13127 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13723 : Nat.Prime 13723 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13829 : Nat.Prime 13829 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13931 : Nat.Prime 13931 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14081 : Nat.Prime 14081 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14153 : Nat.Prime 14153 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14713 : Nat.Prime 14713 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14737 : Nat.Prime 14737 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15881 : Nat.Prime 15881 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_16691 : Nat.Prime 16691 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_17477 : Nat.Prime 17477 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_17609 : Nat.Prime 17609 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_18313 : Nat.Prime 18313 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_19993 : Nat.Prime 19993 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20023 : Nat.Prime 20023 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20117 : Nat.Prime 20117 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20177 : Nat.Prime 20177 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20359 : Nat.Prime 20359 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20441 : Nat.Prime 20441 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20543 : Nat.Prime 20543 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20981 : Nat.Prime 20981 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_21143 : Nat.Prime 21143 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_21247 : Nat.Prime 21247 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_21851 : Nat.Prime 21851 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_22271 : Nat.Prime 22271 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_23909 : Nat.Prime 23909 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_24631 : Nat.Prime 24631 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_25219 : Nat.Prime 25219 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_27077 : Nat.Prime 27077 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_28351 : Nat.Prime 28351 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_28927 : Nat.Prime 28927 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_30133 : Nat.Prime 30133 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_30841 : Nat.Prime 30841 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_31231 : Nat.Prime 31231 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_31477 : Nat.Prime 31477 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_32099 : Nat.Prime 32099 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_32411 : Nat.Prime 32411 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_33083 : Nat.Prime 33083 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_33107 : Nat.Prime 33107 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_33587 : Nat.Prime 33587 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_34483 : Nat.Prime 34483 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_34613 : Nat.Prime 34613 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_35671 : Nat.Prime 35671 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_36709 : Nat.Prime 36709 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_38993 : Nat.Prime 38993 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_39133 : Nat.Prime 39133 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_39509 : Nat.Prime 39509 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_39551 : Nat.Prime 39551 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_39671 : Nat.Prime 39671 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_40429 : Nat.Prime 40429 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_40823 : Nat.Prime 40823 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_42433 : Nat.Prime 42433 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_49603 : Nat.Prime 49603 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_52861 : Nat.Prime 52861 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_52879 : Nat.Prime 52879 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_53633 : Nat.Prime 53633 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_55609 : Nat.Prime 55609 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_56417 : Nat.Prime 56417 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_57223 : Nat.Prime 57223 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_60647 : Nat.Prime 60647 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_64217 : Nat.Prime 64217 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_66037 : Nat.Prime 66037 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_66523 : Nat.Prime 66523 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_67391 : Nat.Prime 67391 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_67447 : Nat.Prime 67447 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_68749 : Nat.Prime 68749 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_78919 : Nat.Prime 78919 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_81773 : Nat.Prime 81773 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_81883 : Nat.Prime 81883 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_84239 : Nat.Prime 84239 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_85303 : Nat.Prime 85303 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_87037 : Nat.Prime 87037 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_89501 : Nat.Prime 89501 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_91033 : Nat.Prime 91033 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_95219 : Nat.Prime 95219 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_96851 : Nat.Prime 96851 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_97187 : Nat.Prime 97187 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_100363 : Nat.Prime 100363 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_100747 : Nat.Prime 100747 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_106669 : Nat.Prime 106669 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_108799 : Nat.Prime 108799 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_111893 : Nat.Prime 111893 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_112543 : Nat.Prime 112543 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_112601 : Nat.Prime 112601 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_114277 : Nat.Prime 114277 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_119617 : Nat.Prime 119617 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_124799 : Nat.Prime 124799 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_133967 : Nat.Prime 133967 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_135019 : Nat.Prime 135019 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_136861 : Nat.Prime 136861 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_145177 : Nat.Prime 145177 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_146291 : Nat.Prime 146291 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_146563 : Nat.Prime 146563 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_153421 : Nat.Prime 153421 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_154579 : Nat.Prime 154579 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_165523 : Nat.Prime 165523 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_167891 : Nat.Prime 167891 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_178781 : Nat.Prime 178781 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_180623 : Nat.Prime 180623 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_181927 : Nat.Prime 181927 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_182389 : Nat.Prime 182389 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_183301 : Nat.Prime 183301 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_189797 : Nat.Prime 189797 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_202637 : Nat.Prime 202637 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_205031 : Nat.Prime 205031 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_213887 : Nat.Prime 213887 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_217937 : Nat.Prime 217937 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_226099 : Nat.Prime 226099 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_251219 : Nat.Prime 251219 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_251483 : Nat.Prime 251483 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_263737 : Nat.Prime 263737 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_294859 : Nat.Prime 294859 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_296251 : Nat.Prime 296251 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_302573 : Nat.Prime 302573 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_324689 : Nat.Prime 324689 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_324763 : Nat.Prime 324763 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_357199 : Nat.Prime 357199 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_391009 : Nat.Prime 391009 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_448871 : Nat.Prime 448871 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_451051 : Nat.Prime 451051 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_453559 : Nat.Prime 453559 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_477047 : Nat.Prime 477047 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_482387 : Nat.Prime 482387 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_495269 : Nat.Prime 495269 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_525923 : Nat.Prime 525923 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_570217 : Nat.Prime 570217 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_584911 : Nat.Prime 584911 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_599309 : Nat.Prime 599309 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_624829 : Nat.Prime 624829 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_683477 : Nat.Prime 683477 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_704069 : Nat.Prime 704069 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_718163 : Nat.Prime 718163 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_741031 : Nat.Prime 741031 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_771961 : Nat.Prime 771961 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_783703 : Nat.Prime 783703 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_810437 : Nat.Prime 810437 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_828221 : Nat.Prime 828221 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_862921 : Nat.Prime 862921 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_930437 : Nat.Prime 930437 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_967397 : Nat.Prime 967397 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_982939 : Nat.Prime 982939 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1029199 : Nat.Prime 1029199 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1049999 : Nat.Prime 1049999 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1076323 : Nat.Prime 1076323 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1133239 : Nat.Prime 1133239 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1162753 : Nat.Prime 1162753 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1216951 : Nat.Prime 1216951 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1247479 : Nat.Prime 1247479 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1350287 : Nat.Prime 1350287 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1356079 : Nat.Prime 1356079 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1509307 : Nat.Prime 1509307 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1519729 : Nat.Prime 1519729 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1724033 : Nat.Prime 1724033 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_1945817 : Nat.Prime 1945817 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2061599 : Nat.Prime 2061599 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2068579 : Nat.Prime 2068579 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2082413 : Nat.Prime 2082413 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2212871 : Nat.Prime 2212871 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2230097 : Nat.Prime 2230097 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2315881 : Nat.Prime 2315881 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2524219 : Nat.Prime 2524219 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2546669 : Nat.Prime 2546669 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2554171 : Nat.Prime 2554171 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2635267 : Nat.Prime 2635267 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2656427 : Nat.Prime 2656427 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2721451 : Nat.Prime 2721451 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_2905921 : Nat.Prime 2905921 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3070973 : Nat.Prime 3070973 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3210101 : Nat.Prime 3210101 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3463069 : Nat.Prime 3463069 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3518759 : Nat.Prime 3518759 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3766577 : Nat.Prime 3766577 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3776317 : Nat.Prime 3776317 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_3796339 : Nat.Prime 3796339 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4158859 : Nat.Prime 4158859 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4265137 : Nat.Prime 4265137 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4289471 : Nat.Prime 4289471 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4294559 : Nat.Prime 4294559 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_4655411 : Nat.Prime 4655411 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5055563 : Nat.Prime 5055563 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5297759 : Nat.Prime 5297759 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5439869 : Nat.Prime 5439869 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5517139 : Nat.Prime 5517139 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5590843 : Nat.Prime 5590843 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_5956663 : Nat.Prime 5956663 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6509689 : Nat.Prime 6509689 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6756241 : Nat.Prime 6756241 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_6867551 : Nat.Prime 6867551 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7392967 : Nat.Prime 7392967 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7503527 : Nat.Prime 7503527 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_7871519 : Nat.Prime 7871519 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8157041 : Nat.Prime 8157041 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8266633 : Nat.Prime 8266633 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8723123 : Nat.Prime 8723123 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_8874181 : Nat.Prime 8874181 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_9901271 : Nat.Prime 9901271 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_10760767 : Nat.Prime 10760767 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_10925389 : Nat.Prime 10925389 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11088149 : Nat.Prime 11088149 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11423669 : Nat.Prime 11423669 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_11514001 : Nat.Prime 11514001 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12398033 : Nat.Prime 12398033 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_12769777 : Nat.Prime 12769777 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13164301 : Nat.Prime 13164301 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13190813 : Nat.Prime 13190813 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13383911 : Nat.Prime 13383911 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_13766867 : Nat.Prime 13766867 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14039341 : Nat.Prime 14039341 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_14666777 : Nat.Prime 14666777 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15394133 : Nat.Prime 15394133 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15472187 : Nat.Prime 15472187 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15515809 : Nat.Prime 15515809 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15841381 : Nat.Prime 15841381 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_15879541 : Nat.Prime 15879541 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_16092997 : Nat.Prime 16092997 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_16243897 : Nat.Prime 16243897 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_16881691 : Nat.Prime 16881691 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_17718919 : Nat.Prime 17718919 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_18138509 : Nat.Prime 18138509 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_18220747 : Nat.Prime 18220747 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_18471199 : Nat.Prime 18471199 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_19129381 : Nat.Prime 19129381 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_19414223 : Nat.Prime 19414223 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20553583 : Nat.Prime 20553583 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_20828309 : Nat.Prime 20828309 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_21330161 : Nat.Prime 21330161 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_23379331 : Nat.Prime 23379331 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_28812437 : Nat.Prime 28812437 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_28951177 : Nat.Prime 28951177 := by norm_num

private theorem prime_oneHundredSixtyThreeFE_31329941 : Nat.Prime 31329941 := by
  apply lucas_primality 31329941 (2 : ZMod 31329941)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (691, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (691, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) = 31329941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_691
      · exact prime_oneHundredSixtyThreeFE_2267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31329941) ^ 15664970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31329941) ^ 6265988 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31329941) ^ 45340 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 31329941) ^ 13820 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_33066533 : Nat.Prime 33066533 := by
  apply lucas_primality 33066533 (2 : ZMod 33066533)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (8266633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (8266633, 1)] : List FactorBlock).map factorBlockValue).prod) = 33066533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_8266633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 33066533) ^ 16533266 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33066533) ^ 4 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_33478609 : Nat.Prime 33478609 := by
  apply lucas_primality 33478609 (11 : ZMod 33478609)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (36709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (36709, 1)] : List FactorBlock).map factorBlockValue).prod) = 33478609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_36709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33478609) ^ 16739304 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33478609) ^ 11159536 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33478609) ^ 1762032 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 33478609) ^ 912 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_33633499 : Nat.Prime 33633499 := by
  apply lucas_primality 33633499 (2 : ZMod 33633499)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (251, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (251, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 33633499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_251
      · exact prime_oneHundredSixtyThreeFE_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33633499) ^ 16816749 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633499) ^ 11211166 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633499) ^ 1462326 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633499) ^ 133998 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33633499) ^ 34638 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_33840707 : Nat.Prime 33840707 := by
  apply lucas_primality 33840707 (2 : ZMod 33840707)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (227, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (227, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 33840707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_131
      · exact prime_oneHundredSixtyThreeFE_227
      · exact prime_oneHundredSixtyThreeFE_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33840707) ^ 16920353 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33840707) ^ 258326 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33840707) ^ 149078 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33840707) ^ 59474 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_37428301 : Nat.Prime 37428301 := by
  apply lucas_primality 37428301 (10 : ZMod 37428301)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (7, 1), (13, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 37428301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 37428301) ^ 18714150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 37428301) ^ 12476100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 37428301) ^ 7485660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 37428301) ^ 5346900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 37428301) ^ 2879100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 37428301) ^ 81900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_37520129 : Nat.Prime 37520129 := by
  apply lucas_primality 37520129 (3 : ZMod 37520129)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (146563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (146563, 1)] : List FactorBlock).map factorBlockValue).prod) = 37520129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_146563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 37520129) ^ 18760064 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37520129) ^ 256 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_38124199 : Nat.Prime 38124199 := by
  apply lucas_primality 38124199 (6 : ZMod 38124199)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (302573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (302573, 1)] : List FactorBlock).map factorBlockValue).prod) = 38124199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_302573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38124199) ^ 19062099 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38124199) ^ 12708066 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38124199) ^ 5446314 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38124199) ^ 126 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_42660323 : Nat.Prime 42660323 := by
  apply lucas_primality 42660323 (2 : ZMod 42660323)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (21330161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (21330161, 1)] : List FactorBlock).map factorBlockValue).prod) = 42660323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_21330161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 42660323) ^ 21330161 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 42660323) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_45875933 : Nat.Prime 45875933 := by
  apply lucas_primality 45875933 (2 : ZMod 45875933)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (145177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (145177, 1)] : List FactorBlock).map factorBlockValue).prod) = 45875933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_79
      · exact prime_oneHundredSixtyThreeFE_145177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45875933) ^ 22937966 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45875933) ^ 580708 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 45875933) ^ 316 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_46199957 : Nat.Prime 46199957 := by
  apply lucas_primality 46199957 (2 : ZMod 46199957)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1049999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1049999, 1)] : List FactorBlock).map factorBlockValue).prod) = 46199957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_1049999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46199957) ^ 23099978 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46199957) ^ 4199996 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46199957) ^ 44 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_48198911 : Nat.Prime 48198911 := by
  apply lucas_primality 48198911 (26 : ZMod 48198911)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (227, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (227, 1), (1249, 1)] : List FactorBlock).map factorBlockValue).prod) = 48198911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_227
      · exact prime_oneHundredSixtyThreeFE_1249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 48198911) ^ 24099455 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (26 : ZMod 48198911) ^ 9639782 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (26 : ZMod 48198911) ^ 2835230 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (26 : ZMod 48198911) ^ 212330 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (26 : ZMod 48198911) ^ 38590 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_49360067 : Nat.Prime 49360067 := by
  apply lucas_primality 49360067 (2 : ZMod 49360067)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (66523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (66523, 1)] : List FactorBlock).map factorBlockValue).prod) = 49360067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_53
      · exact prime_oneHundredSixtyThreeFE_66523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 49360067) ^ 24680033 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 49360067) ^ 7051438 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 49360067) ^ 931322 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 49360067) ^ 742 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_49798079 : Nat.Prime 49798079 := by
  apply lucas_primality 49798079 (7 : ZMod 49798079)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (131, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (131, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 49798079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_131
      · exact prime_oneHundredSixtyThreeFE_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 49798079) ^ 24899039 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 49798079) ^ 4527098 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 49798079) ^ 1345894 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 49798079) ^ 380138 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 49798079) ^ 106634 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_51119701 : Nat.Prime 51119701 := by
  apply lucas_primality 51119701 (7 : ZMod 51119701)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (83, 1), (2053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (83, 1), (2053, 1)] : List FactorBlock).map factorBlockValue).prod) = 51119701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_83
      · exact prime_oneHundredSixtyThreeFE_2053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 51119701) ^ 25559850 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51119701) ^ 17039900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51119701) ^ 10223940 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51119701) ^ 615900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51119701) ^ 24900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_53802349 : Nat.Prime 53802349 := by
  apply lucas_primality 53802349 (2 : ZMod 53802349)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (263737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (263737, 1)] : List FactorBlock).map factorBlockValue).prod) = 53802349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_263737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53802349) ^ 26901174 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 53802349) ^ 17934116 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 53802349) ^ 3164844 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 53802349) ^ 204 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_57164087 : Nat.Prime 57164087 := by
  apply lucas_primality 57164087 (5 : ZMod 57164087)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (41, 2), (347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (41, 2), (347, 1)] : List FactorBlock).map factorBlockValue).prod) = 57164087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_41
      · exact prime_oneHundredSixtyThreeFE_347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 57164087) ^ 28582043 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57164087) ^ 8166298 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57164087) ^ 1394246 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 57164087) ^ 164738 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_59534729 : Nat.Prime 59534729 := by
  apply lucas_primality 59534729 (3 : ZMod 59534729)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (113, 1), (5987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (113, 1), (5987, 1)] : List FactorBlock).map factorBlockValue).prod) = 59534729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_113
      · exact prime_oneHundredSixtyThreeFE_5987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 59534729) ^ 29767364 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 59534729) ^ 5412248 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 59534729) ^ 526856 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 59534729) ^ 9944 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_62972153 : Nat.Prime 62972153 := by
  apply lucas_primality 62972153 (3 : ZMod 62972153)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7871519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7871519, 1)] : List FactorBlock).map factorBlockValue).prod) = 62972153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7871519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 62972153) ^ 31486076 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 62972153) ^ 8 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_67994341 : Nat.Prime 67994341 := by
  apply lucas_primality 67994341 (10 : ZMod 67994341)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (1133239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (1133239, 1)] : List FactorBlock).map factorBlockValue).prod) = 67994341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_1133239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 67994341) ^ 33997170 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 67994341) ^ 22664780 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 67994341) ^ 13598868 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 67994341) ^ 60 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_73381813 : Nat.Prime 73381813 := by
  apply lucas_primality 73381813 (5 : ZMod 73381813)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (124799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (124799, 1)] : List FactorBlock).map factorBlockValue).prod) = 73381813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_124799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 73381813) ^ 36690906 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 73381813) ^ 24460604 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 73381813) ^ 10483116 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 73381813) ^ 588 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_75456967 : Nat.Prime 75456967 := by
  apply lucas_primality 75456967 (6 : ZMod 75456967)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (967397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (967397, 1)] : List FactorBlock).map factorBlockValue).prod) = 75456967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_967397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 75456967) ^ 37728483 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 75456967) ^ 25152322 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 75456967) ^ 5804382 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 75456967) ^ 78 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_81259111 : Nat.Prime 81259111 := by
  apply lucas_primality 81259111 (3 : ZMod 81259111)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (263, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (263, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) = 81259111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_263
      · exact prime_oneHundredSixtyThreeFE_3433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 81259111) ^ 40629555 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81259111) ^ 27086370 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81259111) ^ 16251822 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81259111) ^ 308970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 81259111) ^ 23670 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_84089099 : Nat.Prime 84089099 := by
  apply lucas_primality 84089099 (2 : ZMod 84089099)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2212871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2212871, 1)] : List FactorBlock).map factorBlockValue).prod) = 84089099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_2212871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 84089099) ^ 42044549 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 84089099) ^ 4425742 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 84089099) ^ 38 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_85320647 : Nat.Prime 85320647 := by
  apply lucas_primality 85320647 (5 : ZMod 85320647)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42660323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42660323, 1)] : List FactorBlock).map factorBlockValue).prod) = 85320647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_42660323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 85320647) ^ 42660323 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 85320647) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_91751867 : Nat.Prime 91751867 := by
  apply lucas_primality 91751867 (2 : ZMod 91751867)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (45875933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (45875933, 1)] : List FactorBlock).map factorBlockValue).prod) = 91751867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_45875933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 91751867) ^ 45875933 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 91751867) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_93800671 : Nat.Prime 93800671 := by
  apply lucas_primality 93800671 (21 : ZMod 93800671)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (67, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (67, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 93800671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_67
      · exact prime_oneHundredSixtyThreeFE_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 93800671) ^ 46900335 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (21 : ZMod 93800671) ^ 31266890 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (21 : ZMod 93800671) ^ 18760134 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (21 : ZMod 93800671) ^ 4078290 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (21 : ZMod 93800671) ^ 1400010 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (21 : ZMod 93800671) ^ 46230 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_96397823 : Nat.Prime 96397823 := by
  apply lucas_primality 96397823 (5 : ZMod 96397823)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (48198911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (48198911, 1)] : List FactorBlock).map factorBlockValue).prod) = 96397823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_48198911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 96397823) ^ 48198911 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 96397823) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_110188513 : Nat.Prime 110188513 := by
  apply lucas_primality 110188513 (10 : ZMod 110188513)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 4), (7, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 4), (7, 1), (6073, 1)] : List FactorBlock).map factorBlockValue).prod) = 110188513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_6073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 110188513) ^ 55094256 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 110188513) ^ 36729504 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 110188513) ^ 15741216 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 110188513) ^ 18144 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_121496369 : Nat.Prime 121496369 := by
  apply lucas_primality 121496369 (3 : ZMod 121496369)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (599, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (599, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 121496369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_599
      · exact prime_oneHundredSixtyThreeFE_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 121496369) ^ 60748184 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 121496369) ^ 17356624 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 121496369) ^ 202832 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 121496369) ^ 67088 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_125122399 : Nat.Prime 125122399 := by
  apply lucas_primality 125122399 (3 : ZMod 125122399)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (233, 1), (89501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (233, 1), (89501, 1)] : List FactorBlock).map factorBlockValue).prod) = 125122399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_233
      · exact prime_oneHundredSixtyThreeFE_89501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 125122399) ^ 62561199 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125122399) ^ 41707466 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125122399) ^ 537006 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 125122399) ^ 1398 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_125944307 : Nat.Prime 125944307 := by
  apply lucas_primality 125944307 (2 : ZMod 125944307)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (62972153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (62972153, 1)] : List FactorBlock).map factorBlockValue).prod) = 125944307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_62972153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 125944307) ^ 62972153 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 125944307) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_146266727 : Nat.Prime 146266727 := by
  apply lucas_primality 146266727 (5 : ZMod 146266727)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 2), (33107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 2), (33107, 1)] : List FactorBlock).map factorBlockValue).prod) = 146266727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_33107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 146266727) ^ 73133363 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146266727) ^ 3112058 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 146266727) ^ 4418 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_147328583 : Nat.Prime 147328583 := by
  apply lucas_primality 147328583 (5 : ZMod 147328583)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3511, 1), (20981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3511, 1), (20981, 1)] : List FactorBlock).map factorBlockValue).prod) = 147328583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3511
      · exact prime_oneHundredSixtyThreeFE_20981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 147328583) ^ 73664291 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 147328583) ^ 41962 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 147328583) ^ 7022 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_155234087 : Nat.Prime 155234087 := by
  apply lucas_primality 155234087 (5 : ZMod 155234087)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11088149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11088149, 1)] : List FactorBlock).map factorBlockValue).prod) = 155234087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_11088149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 155234087) ^ 77617043 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 155234087) ^ 22176298 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 155234087) ^ 14 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_156633293 : Nat.Prime 156633293 := by
  apply lucas_primality 156633293 (2 : ZMod 156633293)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (1350287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (1350287, 1)] : List FactorBlock).map factorBlockValue).prod) = 156633293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_1350287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 156633293) ^ 78316646 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156633293) ^ 5401148 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156633293) ^ 116 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_162054799 : Nat.Prime 162054799 := by
  apply lucas_primality 162054799 (3 : ZMod 162054799)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (409, 1), (66037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (409, 1), (66037, 1)] : List FactorBlock).map factorBlockValue).prod) = 162054799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_409
      · exact prime_oneHundredSixtyThreeFE_66037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 162054799) ^ 81027399 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162054799) ^ 54018266 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162054799) ^ 396222 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162054799) ^ 2454 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_180984247 : Nat.Prime 180984247 := by
  apply lucas_primality 180984247 (5 : ZMod 180984247)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (167, 1), (180623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (167, 1), (180623, 1)] : List FactorBlock).map factorBlockValue).prod) = 180984247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_167
      · exact prime_oneHundredSixtyThreeFE_180623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 180984247) ^ 90492123 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 180984247) ^ 60328082 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 180984247) ^ 1083738 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 180984247) ^ 1002 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_200926727 : Nat.Prime 200926727 := by
  apply lucas_primality 200926727 (5 : ZMod 200926727)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (13, 1), (100363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (13, 1), (100363, 1)] : List FactorBlock).map factorBlockValue).prod) = 200926727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_100363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 200926727) ^ 100463363 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 200926727) ^ 28703818 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 200926727) ^ 18266066 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 200926727) ^ 15455902 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 200926727) ^ 2002 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_215431313 : Nat.Prime 215431313 := by
  apply lucas_primality 215431313 (3 : ZMod 215431313)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (389, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (389, 1), (34613, 1)] : List FactorBlock).map factorBlockValue).prod) = 215431313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_389
      · exact prime_oneHundredSixtyThreeFE_34613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 215431313) ^ 107715656 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 215431313) ^ 553808 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 215431313) ^ 6224 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_263817079 : Nat.Prime 263817079 := by
  apply lucas_primality 263817079 (6 : ZMod 263817079)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 4), (18313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 4), (18313, 1)] : List FactorBlock).map factorBlockValue).prod) = 263817079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_18313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 263817079) ^ 131908539 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 263817079) ^ 87939026 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 263817079) ^ 37688154 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 263817079) ^ 14406 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_266857849 : Nat.Prime 266857849 := by
  apply lucas_primality 266857849 (13 : ZMod 266857849)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (41, 1), (30133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (41, 1), (30133, 1)] : List FactorBlock).map factorBlockValue).prod) = 266857849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_41
      · exact prime_oneHundredSixtyThreeFE_30133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 266857849) ^ 133428924 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 266857849) ^ 88952616 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 266857849) ^ 6508728 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 266857849) ^ 8856 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_277199743 : Nat.Prime 277199743 := by
  apply lucas_primality 277199743 (3 : ZMod 277199743)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (46199957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (46199957, 1)] : List FactorBlock).map factorBlockValue).prod) = 277199743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_46199957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 277199743) ^ 138599871 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277199743) ^ 92399914 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 277199743) ^ 6 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_277796221 : Nat.Prime 277796221 := by
  apply lucas_primality 277796221 (2 : ZMod 277796221)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (29, 1), (12281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (29, 1), (12281, 1)] : List FactorBlock).map factorBlockValue).prod) = 277796221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_12281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 277796221) ^ 138898110 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 277796221) ^ 92598740 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 277796221) ^ 55559244 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 277796221) ^ 21368940 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 277796221) ^ 9579180 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 277796221) ^ 22620 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_349951009 : Nat.Prime 349951009 := by
  apply lucas_primality 349951009 (13 : ZMod 349951009)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (283, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (283, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 349951009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_283
      · exact prime_oneHundredSixtyThreeFE_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 349951009) ^ 174975504 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 349951009) ^ 116650336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 349951009) ^ 31813728 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 349951009) ^ 1236576 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 349951009) ^ 298848 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_355616587 : Nat.Prime 355616587 := by
  apply lucas_primality 355616587 (2 : ZMod 355616587)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1519729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1519729, 1)] : List FactorBlock).map factorBlockValue).prod) = 355616587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_1519729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 355616587) ^ 177808293 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 355616587) ^ 118538862 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 355616587) ^ 27355122 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 355616587) ^ 234 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_374283011 : Nat.Prime 374283011 := by
  apply lucas_primality 374283011 (2 : ZMod 374283011)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37428301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37428301, 1)] : List FactorBlock).map factorBlockValue).prod) = 374283011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_37428301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 374283011) ^ 187141505 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374283011) ^ 74856602 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 374283011) ^ 10 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_386847983 : Nat.Prime 386847983 := by
  apply lucas_primality 386847983 (5 : ZMod 386847983)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (683477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (683477, 1)] : List FactorBlock).map factorBlockValue).prod) = 386847983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_283
      · exact prime_oneHundredSixtyThreeFE_683477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 386847983) ^ 193423991 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 386847983) ^ 1366954 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 386847983) ^ 566 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_424095157 : Nat.Prime 424095157 := by
  apply lucas_primality 424095157 (7 : ZMod 424095157)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (223, 1), (17609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (223, 1), (17609, 1)] : List FactorBlock).map factorBlockValue).prod) = 424095157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_223
      · exact prime_oneHundredSixtyThreeFE_17609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 424095157) ^ 212047578 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 424095157) ^ 141365052 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 424095157) ^ 1901772 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 424095157) ^ 24084 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_450401153 : Nat.Prime 450401153 := by
  apply lucas_primality 450401153 (3 : ZMod 450401153)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3518759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3518759, 1)] : List FactorBlock).map factorBlockValue).prod) = 450401153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3518759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 450401153) ^ 225200576 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 450401153) ^ 128 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_476277833 : Nat.Prime 476277833 := by
  apply lucas_primality 476277833 (3 : ZMod 476277833)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59534729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59534729, 1)] : List FactorBlock).map factorBlockValue).prod) = 476277833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_59534729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 476277833) ^ 238138916 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 476277833) ^ 8 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_512095211 : Nat.Prime 512095211 := by
  apply lucas_primality 512095211 (6 : ZMod 512095211)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (4655411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (4655411, 1)] : List FactorBlock).map factorBlockValue).prod) = 512095211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_4655411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 512095211) ^ 256047605 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 512095211) ^ 102419042 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 512095211) ^ 46554110 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 512095211) ^ 110 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_688582513 : Nat.Prime 688582513 := by
  apply lucas_primality 688582513 (10 : ZMod 688582513)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (1097, 1), (1453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (1097, 1), (1453, 1)] : List FactorBlock).map factorBlockValue).prod) = 688582513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_1097
      · exact prime_oneHundredSixtyThreeFE_1453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 688582513) ^ 344291256 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 688582513) ^ 229527504 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 688582513) ^ 627696 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 688582513) ^ 473904 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_705907457 : Nat.Prime 705907457 := by
  apply lucas_primality 705907457 (3 : ZMod 705907457)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (17, 1), (19, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (17, 1), (19, 1), (8537, 1)] : List FactorBlock).map factorBlockValue).prod) = 705907457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_8537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 705907457) ^ 352953728 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 705907457) ^ 41523968 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 705907457) ^ 37153024 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 705907457) ^ 82688 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_712210061 : Nat.Prime 712210061 := by
  apply lucas_primality 712210061 (2 : ZMod 712210061)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (397, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (397, 1), (4721, 1)] : List FactorBlock).map factorBlockValue).prod) = 712210061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_397
      · exact prime_oneHundredSixtyThreeFE_4721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 712210061) ^ 356105030 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 712210061) ^ 142442012 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 712210061) ^ 37484740 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 712210061) ^ 1793980 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 712210061) ^ 150860 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_17203
      · exact prime_oneHundredSixtyThreeFE_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_724216967 : Nat.Prime 724216967 := by
  apply lucas_primality 724216967 (5 : ZMod 724216967)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (139, 1), (13931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (139, 1), (13931, 1)] : List FactorBlock).map factorBlockValue).prod) = 724216967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_139
      · exact prime_oneHundredSixtyThreeFE_13931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 724216967) ^ 362108483 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 724216967) ^ 65837906 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 724216967) ^ 42600998 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 724216967) ^ 5210194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 724216967) ^ 51986 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_762199703 : Nat.Prime 762199703 := by
  apply lucas_primality 762199703 (5 : ZMod 762199703)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (439, 1), (78919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (439, 1), (78919, 1)] : List FactorBlock).map factorBlockValue).prod) = 762199703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_439
      · exact prime_oneHundredSixtyThreeFE_78919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 762199703) ^ 381099851 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 762199703) ^ 69290882 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 762199703) ^ 1736218 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 762199703) ^ 9658 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_813527359 : Nat.Prime 813527359 := by
  apply lucas_primality 813527359 (3 : ZMod 813527359)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (31, 1), (624829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (31, 1), (624829, 1)] : List FactorBlock).map factorBlockValue).prod) = 813527359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_624829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 813527359) ^ 406763679 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 813527359) ^ 271175786 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 813527359) ^ 116218194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 813527359) ^ 26242818 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 813527359) ^ 1302 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_873839891 : Nat.Prime 873839891 := by
  apply lucas_primality 873839891 (2 : ZMod 873839891)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (29, 1), (39133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (29, 1), (39133, 1)] : List FactorBlock).map factorBlockValue).prod) = 873839891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_39133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 873839891) ^ 436919945 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 873839891) ^ 174767978 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 873839891) ^ 124834270 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 873839891) ^ 79439990 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 873839891) ^ 30132410 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 873839891) ^ 22330 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_975809693 : Nat.Prime 975809693 := by
  apply lucas_primality 975809693 (2 : ZMod 975809693)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (31, 1), (113, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (31, 1), (113, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 975809693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_113
      · exact prime_oneHundredSixtyThreeFE_487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 975809693) ^ 487904846 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 975809693) ^ 88709972 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 975809693) ^ 75062284 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 975809693) ^ 31477732 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 975809693) ^ 8635484 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 975809693) ^ 2003716 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1024190423 : Nat.Prime 1024190423 := by
  apply lucas_primality 1024190423 (5 : ZMod 1024190423)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (512095211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (512095211, 1)] : List FactorBlock).map factorBlockValue).prod) = 1024190423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_512095211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1024190423) ^ 512095211 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1024190423) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1059608243 : Nat.Prime 1059608243 := by
  apply lucas_primality 1059608243 (2 : ZMod 1059608243)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (982939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (982939, 1)] : List FactorBlock).map factorBlockValue).prod) = 1059608243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_982939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1059608243) ^ 529804121 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1059608243) ^ 151372606 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1059608243) ^ 96328022 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1059608243) ^ 1078 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1103155829 : Nat.Prime 1103155829 := by
  apply lucas_primality 1103155829 (2 : ZMod 1103155829)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1361, 1), (202637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1361, 1), (202637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1103155829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_1361
      · exact prime_oneHundredSixtyThreeFE_202637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1103155829) ^ 551577914 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103155829) ^ 810548 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1103155829) ^ 5444 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1140641303 : Nat.Prime 1140641303 := by
  apply lucas_primality 1140641303 (5 : ZMod 1140641303)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (10760767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (10760767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140641303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_53
      · exact prime_oneHundredSixtyThreeFE_10760767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1140641303) ^ 570320651 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140641303) ^ 21521534 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140641303) ^ 106 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1243946591 : Nat.Prime 1243946591 := by
  apply lucas_primality 1243946591 (19 : ZMod 1243946591)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (4289471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (4289471, 1)] : List FactorBlock).map factorBlockValue).prod) = 1243946591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_4289471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 1243946591) ^ 621973295 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1243946591) ^ 248789318 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1243946591) ^ 42894710 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 1243946591) ^ 290 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1382996977 : Nat.Prime 1382996977 := by
  apply lucas_primality 1382996977 (5 : ZMod 1382996977)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (28812437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (28812437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1382996977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_28812437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1382996977) ^ 691498488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1382996977) ^ 460998992 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1382996977) ^ 48 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1455684239 : Nat.Prime 1455684239 := by
  apply lucas_primality 1455684239 (7 : ZMod 1455684239)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (7503527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (7503527, 1)] : List FactorBlock).map factorBlockValue).prod) = 1455684239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_97
      · exact prime_oneHundredSixtyThreeFE_7503527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1455684239) ^ 727842119 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1455684239) ^ 15007054 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1455684239) ^ 194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1601216359 : Nat.Prime 1601216359 := by
  apply lucas_primality 1601216359 (7 : ZMod 1601216359)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (38124199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (38124199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601216359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_38124199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1601216359) ^ 800608179 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1601216359) ^ 533738786 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1601216359) ^ 228745194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1601216359) ^ 42 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1747679783 : Nat.Prime 1747679783 := by
  apply lucas_primality 1747679783 (5 : ZMod 1747679783)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (873839891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (873839891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1747679783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_873839891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1747679783) ^ 873839891 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1747679783) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1761920857 : Nat.Prime 1761920857 := by
  apply lucas_primality 1761920857 (5 : ZMod 1761920857)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (8157041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (8157041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1761920857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_8157041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1761920857) ^ 880960428 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1761920857) ^ 587306952 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1761920857) ^ 216 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1937429059 : Nat.Prime 1937429059 := by
  apply lucas_primality 1937429059 (2 : ZMod 1937429059)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (14039341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (14039341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1937429059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_14039341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1937429059) ^ 968714529 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1937429059) ^ 645809686 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1937429059) ^ 84236046 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1937429059) ^ 138 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1958028353 : Nat.Prime 1958028353 := by
  apply lucas_primality 1958028353 (3 : ZMod 1958028353)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (103, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (103, 1), (42433, 1)] : List FactorBlock).map factorBlockValue).prod) = 1958028353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_103
      · exact prime_oneHundredSixtyThreeFE_42433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1958028353) ^ 979014176 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958028353) ^ 279718336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958028353) ^ 19009984 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1958028353) ^ 46144 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2214674977 : Nat.Prime 2214674977 := by
  apply lucas_primality 2214674977 (13 : ZMod 2214674977)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (59, 1), (391009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (59, 1), (391009, 1)] : List FactorBlock).map factorBlockValue).prod) = 2214674977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_59
      · exact prime_oneHundredSixtyThreeFE_391009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 2214674977) ^ 1107337488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2214674977) ^ 738224992 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2214674977) ^ 37536864 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 2214674977) ^ 5664 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2233486663 : Nat.Prime 2233486663 := by
  apply lucas_primality 2233486663 (3 : ZMod 2233486663)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (33840707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (33840707, 1)] : List FactorBlock).map factorBlockValue).prod) = 2233486663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_33840707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2233486663) ^ 1116743331 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2233486663) ^ 744495554 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2233486663) ^ 203044242 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2233486663) ^ 66 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2245698067 : Nat.Prime 2245698067 := by
  apply lucas_primality 2245698067 (2 : ZMod 2245698067)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (374283011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (374283011, 1)] : List FactorBlock).map factorBlockValue).prod) = 2245698067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_374283011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2245698067) ^ 1122849033 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2245698067) ^ 748566022 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2245698067) ^ 6 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2472690329 : Nat.Prime 2472690329 := by
  apply lucas_primality 2472690329 (3 : ZMod 2472690329)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (439, 1), (704069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (439, 1), (704069, 1)] : List FactorBlock).map factorBlockValue).prod) = 2472690329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_439
      · exact prime_oneHundredSixtyThreeFE_704069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2472690329) ^ 1236345164 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2472690329) ^ 5632552 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2472690329) ^ 3512 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2477150981 : Nat.Prime 2477150981 := by
  apply lucas_primality 2477150981 (2 : ZMod 2477150981)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (47, 1), (2635267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (47, 1), (2635267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2477150981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_2635267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2477150981) ^ 1238575490 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477150981) ^ 495430196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477150981) ^ 52705340 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2477150981) ^ 940 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2676380807 : Nat.Prime 2676380807 := by
  apply lucas_primality 2676380807 (5 : ZMod 2676380807)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (787, 1), (154579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (787, 1), (154579, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676380807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_787
      · exact prime_oneHundredSixtyThreeFE_154579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2676380807) ^ 1338190403 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2676380807) ^ 243307346 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2676380807) ^ 3400738 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2676380807) ^ 17314 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2719428071 : Nat.Prime 2719428071 := by
  apply lucas_primality 2719428071 (19 : ZMod 2719428071)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1987, 1), (136861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1987, 1), (136861, 1)] : List FactorBlock).map factorBlockValue).prod) = 2719428071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_1987
      · exact prime_oneHundredSixtyThreeFE_136861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2719428071) ^ 1359714035 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2719428071) ^ 543885614 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2719428071) ^ 1368610 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 2719428071) ^ 19870 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3049582187 : Nat.Prime 3049582187 := by
  apply lucas_primality 3049582187 (2 : ZMod 3049582187)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1489, 1), (146291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1489, 1), (146291, 1)] : List FactorBlock).map factorBlockValue).prod) = 3049582187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_1489
      · exact prime_oneHundredSixtyThreeFE_146291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3049582187) ^ 1524791093 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3049582187) ^ 435654598 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3049582187) ^ 2048074 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3049582187) ^ 20846 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3187594301 : Nat.Prime 3187594301 := by
  apply lucas_primality 3187594301 (2 : ZMod 3187594301)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (43, 1), (67391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (43, 1), (67391, 1)] : List FactorBlock).map factorBlockValue).prod) = 3187594301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_43
      · exact prime_oneHundredSixtyThreeFE_67391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3187594301) ^ 1593797150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3187594301) ^ 637518860 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3187594301) ^ 289781300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3187594301) ^ 74130100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3187594301) ^ 47300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4303428007 : Nat.Prime 4303428007 := by
  apply lucas_primality 4303428007 (3 : ZMod 4303428007)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 2), (324689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 2), (324689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4303428007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_324689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4303428007) ^ 2151714003 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303428007) ^ 1434476002 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303428007) ^ 91562298 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4303428007) ^ 13254 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5161293727 : Nat.Prime 5161293727 := by
  apply lucas_primality 5161293727 (3 : ZMod 5161293727)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (499, 1), (55609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (499, 1), (55609, 1)] : List FactorBlock).map factorBlockValue).prod) = 5161293727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_499
      · exact prime_oneHundredSixtyThreeFE_55609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5161293727) ^ 2580646863 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5161293727) ^ 1720431242 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5161293727) ^ 166493346 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5161293727) ^ 10343274 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 5161293727) ^ 92814 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5211444731 : Nat.Prime 5211444731 := by
  apply lucas_primality 5211444731 (2 : ZMod 5211444731)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (71, 1), (307, 1), (23909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (71, 1), (307, 1), (23909, 1)] : List FactorBlock).map factorBlockValue).prod) = 5211444731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_71
      · exact prime_oneHundredSixtyThreeFE_307
      · exact prime_oneHundredSixtyThreeFE_23909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5211444731) ^ 2605722365 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211444731) ^ 1042288946 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211444731) ^ 73400630 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211444731) ^ 16975390 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5211444731) ^ 217970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5388682799 : Nat.Prime 5388682799 := by
  apply lucas_primality 5388682799 (11 : ZMod 5388682799)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14699, 1), (183301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14699, 1), (183301, 1)] : List FactorBlock).map factorBlockValue).prod) = 5388682799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_14699
      · exact prime_oneHundredSixtyThreeFE_183301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 5388682799) ^ 2694341399 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5388682799) ^ 366602 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5388682799) ^ 29398 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6290781691 : Nat.Prime 6290781691 := by
  apply lucas_primality 6290781691 (2 : ZMod 6290781691)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3109, 1), (67447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3109, 1), (67447, 1)] : List FactorBlock).map factorBlockValue).prod) = 6290781691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_3109
      · exact prime_oneHundredSixtyThreeFE_67447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6290781691) ^ 3145390845 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6290781691) ^ 2096927230 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6290781691) ^ 1258156338 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6290781691) ^ 2023410 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6290781691) ^ 93270 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6972298243 : Nat.Prime 6972298243 := by
  apply lucas_primality 6972298243 (2 : ZMod 6972298243)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (12769777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (12769777, 1)] : List FactorBlock).map factorBlockValue).prod) = 6972298243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_12769777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6972298243) ^ 3486149121 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6972298243) ^ 2324099414 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6972298243) ^ 996042606 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6972298243) ^ 536330634 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6972298243) ^ 546 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7258946483 : Nat.Prime 7258946483 := by
  apply lucas_primality 7258946483 (2 : ZMod 7258946483)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (199, 1), (111893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (199, 1), (111893, 1)] : List FactorBlock).map factorBlockValue).prod) = 7258946483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_163
      · exact prime_oneHundredSixtyThreeFE_199
      · exact prime_oneHundredSixtyThreeFE_111893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7258946483) ^ 3629473241 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7258946483) ^ 44533414 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7258946483) ^ 36477118 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7258946483) ^ 64874 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8135273591 : Nat.Prime 8135273591 := by
  apply lucas_primality 8135273591 (7 : ZMod 8135273591)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (813527359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (813527359, 1)] : List FactorBlock).map factorBlockValue).prod) = 8135273591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_813527359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 8135273591) ^ 4067636795 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8135273591) ^ 1627054718 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8135273591) ^ 10 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8657208337 : Nat.Prime 8657208337 := by
  apply lucas_primality 8657208337 (11 : ZMod 8657208337)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (19, 1), (1356079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (19, 1), (1356079, 1)] : List FactorBlock).map factorBlockValue).prod) = 8657208337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_1356079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 8657208337) ^ 4328604168 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8657208337) ^ 2885736112 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8657208337) ^ 1236744048 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8657208337) ^ 455642544 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8657208337) ^ 6384 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_9993470317 : Nat.Prime 9993470317 := by
  apply lucas_primality 9993470317 (5 : ZMod 9993470317)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (17718919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (17718919, 1)] : List FactorBlock).map factorBlockValue).prod) = 9993470317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_17718919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9993470317) ^ 4996735158 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9993470317) ^ 3331156772 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9993470317) ^ 212627028 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9993470317) ^ 564 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_11391132479 : Nat.Prime 11391132479 := by
  apply lucas_primality 11391132479 (11 : ZMod 11391132479)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (281, 1), (31231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (281, 1), (31231, 1)] : List FactorBlock).map factorBlockValue).prod) = 11391132479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_59
      · exact prime_oneHundredSixtyThreeFE_281
      · exact prime_oneHundredSixtyThreeFE_31231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 11391132479) ^ 5695566239 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 11391132479) ^ 1035557498 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 11391132479) ^ 193070042 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 11391132479) ^ 40537838 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 11391132479) ^ 364738 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_11750453837 : Nat.Prime 11750453837 := by
  apply lucas_primality 11750453837 (2 : ZMod 11750453837)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (67, 1), (857, 1), (4651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (67, 1), (857, 1), (4651, 1)] : List FactorBlock).map factorBlockValue).prod) = 11750453837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_67
      · exact prime_oneHundredSixtyThreeFE_857
      · exact prime_oneHundredSixtyThreeFE_4651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11750453837) ^ 5875226918 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11750453837) ^ 1068223076 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11750453837) ^ 175379908 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11750453837) ^ 13711148 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11750453837) ^ 2526436 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_12146541829 : Nat.Prime 12146541829 := by
  apply lucas_primality 12146541829 (2 : ZMod 12146541829)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (401, 1), (2524219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (401, 1), (2524219, 1)] : List FactorBlock).map factorBlockValue).prod) = 12146541829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_401
      · exact prime_oneHundredSixtyThreeFE_2524219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12146541829) ^ 6073270914 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146541829) ^ 4048847276 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146541829) ^ 30290628 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12146541829) ^ 4812 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_13640512573 : Nat.Prime 13640512573 := by
  apply lucas_primality 13640512573 (2 : ZMod 13640512573)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23, 2), (167, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23, 2), (167, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 13640512573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_167
      · exact prime_oneHundredSixtyThreeFE_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13640512573) ^ 6820256286 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13640512573) ^ 4546837524 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13640512573) ^ 593065764 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13640512573) ^ 81679716 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13640512573) ^ 3180348 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_15652436347 : Nat.Prime 15652436347 := by
  apply lucas_primality 15652436347 (2 : ZMod 15652436347)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (6491, 1), (133967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (6491, 1), (133967, 1)] : List FactorBlock).map factorBlockValue).prod) = 15652436347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_6491
      · exact prime_oneHundredSixtyThreeFE_133967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15652436347) ^ 7826218173 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15652436347) ^ 5217478782 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15652436347) ^ 2411406 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 15652436347) ^ 116838 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_17419031593 : Nat.Prime 17419031593 := by
  apply lucas_primality 17419031593 (7 : ZMod 17419031593)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (137, 1), (5297759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (137, 1), (5297759, 1)] : List FactorBlock).map factorBlockValue).prod) = 17419031593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_137
      · exact prime_oneHundredSixtyThreeFE_5297759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17419031593) ^ 8709515796 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17419031593) ^ 5806343864 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17419031593) ^ 127146216 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17419031593) ^ 3288 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_18053290127 : Nat.Prime 18053290127 := by
  apply lucas_primality 18053290127 (5 : ZMod 18053290127)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4639, 1), (1945817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4639, 1), (1945817, 1)] : List FactorBlock).map factorBlockValue).prod) = 18053290127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_4639
      · exact prime_oneHundredSixtyThreeFE_1945817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18053290127) ^ 9026645063 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 18053290127) ^ 3891634 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 18053290127) ^ 9278 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_18330456427 : Nat.Prime 18330456427 := by
  apply lucas_primality 18330456427 (3 : ZMod 18330456427)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (79, 1), (1247479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (79, 1), (1247479, 1)] : List FactorBlock).map factorBlockValue).prod) = 18330456427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_79
      · exact prime_oneHundredSixtyThreeFE_1247479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 18330456427) ^ 9165228213 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 18330456427) ^ 6110152142 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 18330456427) ^ 591305046 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 18330456427) ^ 232031094 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 18330456427) ^ 14694 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_19516193861 : Nat.Prime 19516193861 := by
  apply lucas_primality 19516193861 (2 : ZMod 19516193861)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (975809693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (975809693, 1)] : List FactorBlock).map factorBlockValue).prod) = 19516193861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_975809693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19516193861) ^ 9758096930 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19516193861) ^ 3903238772 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19516193861) ^ 20 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_25450010249 : Nat.Prime 25450010249 := by
  apply lucas_primality 25450010249 (3 : ZMod 25450010249)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (317, 1), (771961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (317, 1), (771961, 1)] : List FactorBlock).map factorBlockValue).prod) = 25450010249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_317
      · exact prime_oneHundredSixtyThreeFE_771961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25450010249) ^ 12725005124 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25450010249) ^ 1957693096 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25450010249) ^ 80283944 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 25450010249) ^ 32968 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_30115412879 : Nat.Prime 30115412879 := by
  apply lucas_primality 30115412879 (13 : ZMod 30115412879)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (97, 1), (155234087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (97, 1), (155234087, 1)] : List FactorBlock).map factorBlockValue).prod) = 30115412879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_97
      · exact prime_oneHundredSixtyThreeFE_155234087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 30115412879) ^ 15057706439 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 30115412879) ^ 310468174 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 30115412879) ^ 194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_37404096853 : Nat.Prime 37404096853 := by
  apply lucas_primality 37404096853 (2 : ZMod 37404096853)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (971, 1), (3210101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (971, 1), (3210101, 1)] : List FactorBlock).map factorBlockValue).prod) = 37404096853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_971
      · exact prime_oneHundredSixtyThreeFE_3210101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37404096853) ^ 18702048426 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404096853) ^ 12468032284 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404096853) ^ 38521212 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404096853) ^ 11652 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_42624903721 : Nat.Prime 42624903721 := by
  apply lucas_primality 42624903721 (17 : ZMod 42624903721)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (1283, 1), (39551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (1283, 1), (39551, 1)] : List FactorBlock).map factorBlockValue).prod) = 42624903721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_1283
      · exact prime_oneHundredSixtyThreeFE_39551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 42624903721) ^ 21312451860 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (17 : ZMod 42624903721) ^ 14208301240 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (17 : ZMod 42624903721) ^ 8524980744 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (17 : ZMod 42624903721) ^ 6089271960 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (17 : ZMod 42624903721) ^ 33222840 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (17 : ZMod 42624903721) ^ 1077720 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_63354172991 : Nat.Prime 63354172991 := by
  apply lucas_primality 63354172991 (7 : ZMod 63354172991)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2063, 1), (3070973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2063, 1), (3070973, 1)] : List FactorBlock).map factorBlockValue).prod) = 63354172991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_2063
      · exact prime_oneHundredSixtyThreeFE_3070973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 63354172991) ^ 31677086495 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 63354172991) ^ 12670834598 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 63354172991) ^ 30709730 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 63354172991) ^ 20630 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_68860975921 : Nat.Prime 68860975921 := by
  apply lucas_primality 68860975921 (14 : ZMod 68860975921)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (67, 1), (73, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (67, 1), (73, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) = 68860975921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_67
      · exact prime_oneHundredSixtyThreeFE_73
      · exact prime_oneHundredSixtyThreeFE_5333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 68860975921) ^ 34430487960 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 22953658640 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 13772195184 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 6260088720 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 1027775760 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 943301040 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 68860975921) ^ 12912240 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_76815192407 : Nat.Prime 76815192407 := by
  apply lucas_primality 76815192407 (5 : ZMod 76815192407)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (509, 1), (75456967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (509, 1), (75456967, 1)] : List FactorBlock).map factorBlockValue).prod) = 76815192407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_509
      · exact prime_oneHundredSixtyThreeFE_75456967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 76815192407) ^ 38407596203 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76815192407) ^ 150913934 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 76815192407) ^ 1018 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_78674598283 : Nat.Prime 78674598283 := by
  apply lucas_primality 78674598283 (2 : ZMod 78674598283)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (110188513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (110188513, 1)] : List FactorBlock).map factorBlockValue).prod) = 78674598283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_110188513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78674598283) ^ 39337299141 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 78674598283) ^ 26224866094 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 78674598283) ^ 11239228326 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 78674598283) ^ 4627917546 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 78674598283) ^ 714 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_79126090529 : Nat.Prime 79126090529 := by
  apply lucas_primality 79126090529 (3 : ZMod 79126090529)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2472690329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2472690329, 1)] : List FactorBlock).map factorBlockValue).prod) = 79126090529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_2472690329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 79126090529) ^ 39563045264 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 79126090529) ^ 32 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_97975351717 : Nat.Prime 97975351717 := by
  apply lucas_primality 97975351717 (6 : ZMod 97975351717)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (29, 1), (4001, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (29, 1), (4001, 1), (6397, 1)] : List FactorBlock).map factorBlockValue).prod) = 97975351717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_4001
      · exact prime_oneHundredSixtyThreeFE_6397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 97975351717) ^ 48987675858 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 97975351717) ^ 32658450572 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 97975351717) ^ 8906850156 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 97975351717) ^ 3378460404 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 97975351717) ^ 24487716 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 97975351717) ^ 15315828 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_103340194213 : Nat.Prime 103340194213 := by
  apply lucas_primality 103340194213 (2 : ZMod 103340194213)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (277796221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (277796221, 1)] : List FactorBlock).map factorBlockValue).prod) = 103340194213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_277796221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 103340194213) ^ 51670097106 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103340194213) ^ 34446731404 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103340194213) ^ 3333554652 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 103340194213) ^ 372 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_122990042251 : Nat.Prime 122990042251 := by
  apply lucas_primality 122990042251 (10 : ZMod 122990042251)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 3), (18220747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 3), (18220747, 1)] : List FactorBlock).map factorBlockValue).prod) = 122990042251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_18220747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 122990042251) ^ 61495021125 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 122990042251) ^ 40996680750 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 122990042251) ^ 24598008450 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 122990042251) ^ 6750 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_154731727439 : Nat.Prime 154731727439 := by
  apply lucas_primality 154731727439 (7 : ZMod 154731727439)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (277, 1), (409, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (277, 1), (409, 1), (15881, 1)] : List FactorBlock).map factorBlockValue).prod) = 154731727439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_43
      · exact prime_oneHundredSixtyThreeFE_277
      · exact prime_oneHundredSixtyThreeFE_409
      · exact prime_oneHundredSixtyThreeFE_15881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 154731727439) ^ 77365863719 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154731727439) ^ 3598412266 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154731727439) ^ 558598294 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154731727439) ^ 378317182 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 154731727439) ^ 9743198 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_164243438209 : Nat.Prime 164243438209 := by
  apply lucas_primality 164243438209 (13 : ZMod 164243438209)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 4), (15841381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 4), (15841381, 1)] : List FactorBlock).map factorBlockValue).prod) = 164243438209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_15841381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 164243438209) ^ 82121719104 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 164243438209) ^ 54747812736 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 164243438209) ^ 10368 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_166415597207 : Nat.Prime 166415597207 := by
  apply lucas_primality 166415597207 (5 : ZMod 166415597207)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1367, 1), (2963, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1367, 1), (2963, 1), (20543, 1)] : List FactorBlock).map factorBlockValue).prod) = 166415597207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_1367
      · exact prime_oneHundredSixtyThreeFE_2963
      · exact prime_oneHundredSixtyThreeFE_20543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 166415597207) ^ 83207798603 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 166415597207) ^ 121737818 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 166415597207) ^ 56164562 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 166415597207) ^ 8100842 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_208236502417 : Nat.Prime 208236502417 := by
  apply lucas_primality 208236502417 (5 : ZMod 208236502417)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (14713, 1), (294859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (14713, 1), (294859, 1)] : List FactorBlock).map factorBlockValue).prod) = 208236502417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_14713
      · exact prime_oneHundredSixtyThreeFE_294859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 208236502417) ^ 104118251208 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 208236502417) ^ 69412167472 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 208236502417) ^ 14153232 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 208236502417) ^ 706224 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_240516622601 : Nat.Prime 240516622601 := by
  apply lucas_primality 240516622601 (3 : ZMod 240516622601)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (30841, 1), (38993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (30841, 1), (38993, 1)] : List FactorBlock).map factorBlockValue).prod) = 240516622601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_30841
      · exact prime_oneHundredSixtyThreeFE_38993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 240516622601) ^ 120258311300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 240516622601) ^ 48103324520 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 240516622601) ^ 7798600 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 240516622601) ^ 6168200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_253568171789 : Nat.Prime 253568171789 := by
  apply lucas_primality 253568171789 (2 : ZMod 253568171789)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 2), (821, 1), (213887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 2), (821, 1), (213887, 1)] : List FactorBlock).map factorBlockValue).prod) = 253568171789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_821
      · exact prime_oneHundredSixtyThreeFE_213887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 253568171789) ^ 126784085894 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 253568171789) ^ 13345693252 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 253568171789) ^ 308852828 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 253568171789) ^ 1185524 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_286883487091 : Nat.Prime 286883487091 := by
  apply lucas_primality 286883487091 (2 : ZMod 286883487091)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (3187594301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (3187594301, 1)] : List FactorBlock).map factorBlockValue).prod) = 286883487091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_3187594301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 286883487091) ^ 143441743545 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 286883487091) ^ 95627829030 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 286883487091) ^ 57376697418 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 286883487091) ^ 90 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_293605974401 : Nat.Prime 293605974401 := by
  apply lucas_primality 293605974401 (6 : ZMod 293605974401)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (91751867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (91751867, 1)] : List FactorBlock).map factorBlockValue).prod) = 293605974401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_91751867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 293605974401) ^ 146802987200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 293605974401) ^ 58721194880 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 293605974401) ^ 3200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_306552390803 : Nat.Prime 306552390803 := by
  apply lucas_primality 306552390803 (2 : ZMod 306552390803)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (947, 1), (1216951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (947, 1), (1216951, 1)] : List FactorBlock).map factorBlockValue).prod) = 306552390803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_947
      · exact prime_oneHundredSixtyThreeFE_1216951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 306552390803) ^ 153276195401 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306552390803) ^ 43793198686 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306552390803) ^ 16134336358 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306552390803) ^ 323708966 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306552390803) ^ 251902 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_321650467769 : Nat.Prime 321650467769 := by
  apply lucas_primality 321650467769 (3 : ZMod 321650467769)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (61, 1), (1669, 1), (56417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (61, 1), (1669, 1), (56417, 1)] : List FactorBlock).map factorBlockValue).prod) = 321650467769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_61
      · exact prime_oneHundredSixtyThreeFE_1669
      · exact prime_oneHundredSixtyThreeFE_56417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 321650467769) ^ 160825233884 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 321650467769) ^ 45950066824 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 321650467769) ^ 5272958488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 321650467769) ^ 192720472 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 321650467769) ^ 5701304 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_354262255981 : Nat.Prime 354262255981 := by
  apply lucas_primality 354262255981 (2 : ZMod 354262255981)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (35671, 1), (165523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (35671, 1), (165523, 1)] : List FactorBlock).map factorBlockValue).prod) = 354262255981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_35671
      · exact prime_oneHundredSixtyThreeFE_165523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 354262255981) ^ 177131127990 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 354262255981) ^ 118087418660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 354262255981) ^ 70852451196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 354262255981) ^ 9931380 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 354262255981) ^ 2140260 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_398545109059 : Nat.Prime 398545109059 := by
  apply lucas_primality 398545109059 (2 : ZMod 398545109059)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (61, 1), (3413, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (61, 1), (3413, 1), (8623, 1)] : List FactorBlock).map factorBlockValue).prod) = 398545109059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_61
      · exact prime_oneHundredSixtyThreeFE_3413
      · exact prime_oneHundredSixtyThreeFE_8623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 398545109059) ^ 199272554529 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398545109059) ^ 132848369686 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398545109059) ^ 10771489434 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398545109059) ^ 6533526378 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398545109059) ^ 116772666 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 398545109059) ^ 46218846 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_419229335099 : Nat.Prime 419229335099 := by
  apply lucas_primality 419229335099 (6 : ZMod 419229335099)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (139, 1), (215431313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (139, 1), (215431313, 1)] : List FactorBlock).map factorBlockValue).prod) = 419229335099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_139
      · exact prime_oneHundredSixtyThreeFE_215431313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 419229335099) ^ 209614667549 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 419229335099) ^ 59889905014 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 419229335099) ^ 3016038382 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 419229335099) ^ 1946 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_429675488113 : Nat.Prime 429675488113 := by
  apply lucas_primality 429675488113 (5 : ZMod 429675488113)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (688582513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (688582513, 1)] : List FactorBlock).map factorBlockValue).prod) = 429675488113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_688582513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 429675488113) ^ 214837744056 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 429675488113) ^ 143225162704 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 429675488113) ^ 33051960624 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 429675488113) ^ 624 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_501133510967 : Nat.Prime 501133510967 := by
  apply lucas_primality 501133510967 (10 : ZMod 501133510967)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (100747, 1), (226099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (100747, 1), (226099, 1)] : List FactorBlock).map factorBlockValue).prod) = 501133510967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_100747
      · exact prime_oneHundredSixtyThreeFE_226099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 501133510967) ^ 250566755483 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 501133510967) ^ 45557591906 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 501133510967) ^ 4974178 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 501133510967) ^ 2216434 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_538430806117 : Nat.Prime 538430806117 := by
  apply lucas_primality 538430806117 (14 : ZMod 538430806117)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (712210061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (712210061, 1)] : List FactorBlock).map factorBlockValue).prod) = 538430806117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_712210061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 538430806117) ^ 269215403058 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 538430806117) ^ 179476935372 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 538430806117) ^ 76918686588 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (14 : ZMod 538430806117) ^ 756 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_550617305201 : Nat.Prime 550617305201 := by
  apply lucas_primality 550617305201 (3 : ZMod 550617305201)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 2), (61, 1), (233, 1), (96851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 2), (61, 1), (233, 1), (96851, 1)] : List FactorBlock).map factorBlockValue).prod) = 550617305201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_61
      · exact prime_oneHundredSixtyThreeFE_233
      · exact prime_oneHundredSixtyThreeFE_96851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 550617305201) ^ 275308652600 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 550617305201) ^ 110123461040 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 550617305201) ^ 9026513200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 550617305201) ^ 2363164400 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 550617305201) ^ 5685200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_775379227789 : Nat.Prime 775379227789 := by
  apply lucas_primality 775379227789 (7 : ZMod 775379227789)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (1958028353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (1958028353, 1)] : List FactorBlock).map factorBlockValue).prod) = 775379227789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_1958028353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 775379227789) ^ 387689613894 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 775379227789) ^ 258459742596 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 775379227789) ^ 70489020708 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 775379227789) ^ 396 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_781599851401 : Nat.Prime 781599851401 := by
  apply lucas_primality 781599851401 (11 : ZMod 781599851401)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (233, 1), (5590843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (233, 1), (5590843, 1)] : List FactorBlock).map factorBlockValue).prod) = 781599851401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_233
      · exact prime_oneHundredSixtyThreeFE_5590843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 781599851401) ^ 390799925700 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 781599851401) ^ 260533283800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 781599851401) ^ 156319970280 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 781599851401) ^ 3354505800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 781599851401) ^ 139800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_822324788251 : Nat.Prime 822324788251 := by
  apply lucas_primality 822324788251 (2 : ZMod 822324788251)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (156633293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (156633293, 1)] : List FactorBlock).map factorBlockValue).prod) = 822324788251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_156633293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 822324788251) ^ 411162394125 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 822324788251) ^ 274108262750 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 822324788251) ^ 164464957650 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 822324788251) ^ 117474969750 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 822324788251) ^ 5250 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1012727922251 : Nat.Prime 1012727922251 := by
  apply lucas_primality 1012727922251 (2 : ZMod 1012727922251)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 2), (33478609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 2), (33478609, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012727922251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_33478609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1012727922251) ^ 506363961125 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012727922251) ^ 202545584450 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012727922251) ^ 92066174750 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1012727922251) ^ 30250 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1033111669397 : Nat.Prime 1033111669397 := by
  apply lucas_primality 1033111669397 (2 : ZMod 1033111669397)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (211, 1), (787, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (211, 1), (787, 1), (53633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033111669397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_211
      · exact prime_oneHundredSixtyThreeFE_787
      · exact prime_oneHundredSixtyThreeFE_53633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1033111669397) ^ 516555834698 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033111669397) ^ 35624540324 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033111669397) ^ 4896263836 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033111669397) ^ 1312721308 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033111669397) ^ 19262612 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2182715280589 : Nat.Prime 2182715280589 := by
  apply lucas_primality 2182715280589 (10 : ZMod 2182715280589)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (311, 1), (503, 1), (1162753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (311, 1), (503, 1), (1162753, 1)] : List FactorBlock).map factorBlockValue).prod) = 2182715280589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_311
      · exact prime_oneHundredSixtyThreeFE_503
      · exact prime_oneHundredSixtyThreeFE_1162753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2182715280589) ^ 1091357640294 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2182715280589) ^ 727571760196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2182715280589) ^ 7018377108 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2182715280589) ^ 4339394196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 2182715280589) ^ 1877196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2393862198593 : Nat.Prime 2393862198593 := by
  apply lucas_primality 2393862198593 (3 : ZMod 2393862198593)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (37404096853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (37404096853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2393862198593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_37404096853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2393862198593) ^ 1196931099296 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2393862198593) ^ 64 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3138405103061 : Nat.Prime 3138405103061 := by
  apply lucas_primality 3138405103061 (2 : ZMod 3138405103061)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1747, 1), (6379, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1747, 1), (6379, 1), (14081, 1)] : List FactorBlock).map factorBlockValue).prod) = 3138405103061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_1747
      · exact prime_oneHundredSixtyThreeFE_6379
      · exact prime_oneHundredSixtyThreeFE_14081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3138405103061) ^ 1569202551530 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138405103061) ^ 627681020612 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138405103061) ^ 1796453980 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138405103061) ^ 491990140 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3138405103061) ^ 222882260 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3659985909017 : Nat.Prime 3659985909017 := by
  apply lucas_primality 3659985909017 (3 : ZMod 3659985909017)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (113, 1), (263, 1), (15394133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (113, 1), (263, 1), (15394133, 1)] : List FactorBlock).map factorBlockValue).prod) = 3659985909017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_113
      · exact prime_oneHundredSixtyThreeFE_263
      · exact prime_oneHundredSixtyThreeFE_15394133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3659985909017) ^ 1829992954508 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3659985909017) ^ 32389255832 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3659985909017) ^ 13916296232 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3659985909017) ^ 237752 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4257218355043 : Nat.Prime 4257218355043 := by
  apply lucas_primality 4257218355043 (3 : ZMod 4257218355043)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (9993470317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (9993470317, 1)] : List FactorBlock).map factorBlockValue).prod) = 4257218355043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_71
      · exact prime_oneHundredSixtyThreeFE_9993470317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4257218355043) ^ 2128609177521 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4257218355043) ^ 1419072785014 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4257218355043) ^ 59960821902 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4257218355043) ^ 426 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4384095043693 : Nat.Prime 4384095043693 := by
  apply lucas_primality 4384095043693 (5 : ZMod 4384095043693)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13, 1), (331, 1), (857, 1), (14153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13, 1), (331, 1), (857, 1), (14153, 1)] : List FactorBlock).map factorBlockValue).prod) = 4384095043693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_331
      · exact prime_oneHundredSixtyThreeFE_857
      · exact prime_oneHundredSixtyThreeFE_14153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4384095043693) ^ 2192047521846 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 1461365014564 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 626299291956 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 337238080284 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 13245000132 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 5115630156 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 4384095043693) ^ 309764364 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4701632561939 : Nat.Prime 4701632561939 := by
  apply lucas_primality 4701632561939 (2 : ZMod 4701632561939)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (73, 1), (2477150981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (73, 1), (2477150981, 1)] : List FactorBlock).map factorBlockValue).prod) = 4701632561939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_73
      · exact prime_oneHundredSixtyThreeFE_2477150981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4701632561939) ^ 2350816280969 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701632561939) ^ 361664043226 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701632561939) ^ 64405925506 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4701632561939) ^ 1898 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4808642605621 : Nat.Prime 4808642605621 := by
  apply lucas_primality 4808642605621 (10 : ZMod 4808642605621)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 2), (103, 1), (15879541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 2), (103, 1), (15879541, 1)] : List FactorBlock).map factorBlockValue).prod) = 4808642605621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_103
      · exact prime_oneHundredSixtyThreeFE_15879541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4808642605621) ^ 2404321302810 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4808642605621) ^ 1602880868540 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4808642605621) ^ 961728521124 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4808642605621) ^ 686948943660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4808642605621) ^ 46685850540 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4808642605621) ^ 302820 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5289680726969 : Nat.Prime 5289680726969 := by
  apply lucas_primality 5289680726969 (6 : ZMod 5289680726969)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (83, 1), (724216967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (83, 1), (724216967, 1)] : List FactorBlock).map factorBlockValue).prod) = 5289680726969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_83
      · exact prime_oneHundredSixtyThreeFE_724216967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5289680726969) ^ 2644840363484 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5289680726969) ^ 480880066088 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5289680726969) ^ 63731093096 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 5289680726969) ^ 7304 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6089327402311 : Nat.Prime 6089327402311 := by
  apply lucas_primality 6089327402311 (15 : ZMod 6089327402311)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (43, 1), (353, 1), (495269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (43, 1), (353, 1), (495269, 1)] : List FactorBlock).map factorBlockValue).prod) = 6089327402311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_43
      · exact prime_oneHundredSixtyThreeFE_353
      · exact prime_oneHundredSixtyThreeFE_495269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 6089327402311) ^ 3044663701155 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 6089327402311) ^ 2029775800770 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 6089327402311) ^ 1217865480462 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 6089327402311) ^ 141612265170 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 6089327402311) ^ 17250219270 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 6089327402311) ^ 12294990 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6320159937277 : Nat.Prime 6320159937277 := by
  apply lucas_primality 6320159937277 (2 : ZMod 6320159937277)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (691, 1), (762199703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (691, 1), (762199703, 1)] : List FactorBlock).map factorBlockValue).prod) = 6320159937277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_691
      · exact prime_oneHundredSixtyThreeFE_762199703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6320159937277) ^ 3160079968638 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6320159937277) ^ 2106719979092 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6320159937277) ^ 9146396436 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6320159937277) ^ 8292 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7210846391621 : Nat.Prime 7210846391621 := by
  apply lucas_primality 7210846391621 (2 : ZMod 7210846391621)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (757, 1), (476277833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (757, 1), (476277833, 1)] : List FactorBlock).map factorBlockValue).prod) = 7210846391621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_757
      · exact prime_oneHundredSixtyThreeFE_476277833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7210846391621) ^ 3605423195810 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7210846391621) ^ 1442169278324 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7210846391621) ^ 9525556660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7210846391621) ^ 15140 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7653784202809 : Nat.Prime 7653784202809 := by
  apply lucas_primality 7653784202809 (7 : ZMod 7653784202809)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (181, 1), (1761920857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (181, 1), (1761920857, 1)] : List FactorBlock).map factorBlockValue).prod) = 7653784202809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_181
      · exact prime_oneHundredSixtyThreeFE_1761920857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7653784202809) ^ 3826892101404 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 7653784202809) ^ 2551261400936 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 7653784202809) ^ 42286100568 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 7653784202809) ^ 4344 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7741607445889 : Nat.Prime 7741607445889 := by
  apply lucas_primality 7741607445889 (13 : ZMod 7741607445889)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (31, 1), (127, 1), (293, 1), (17477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (31, 1), (127, 1), (293, 1), (17477, 1)] : List FactorBlock).map factorBlockValue).prod) = 7741607445889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_127
      · exact prime_oneHundredSixtyThreeFE_293
      · exact prime_oneHundredSixtyThreeFE_17477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 7741607445889) ^ 3870803722944 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7741607445889) ^ 2580535815296 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7741607445889) ^ 249729272448 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7741607445889) ^ 60957538944 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7741607445889) ^ 26421868416 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 7741607445889) ^ 442959744 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_9679721012201 : Nat.Prime 9679721012201 := by
  apply lucas_primality 9679721012201 (13 : ZMod 9679721012201)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (1439, 1), (33633499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (1439, 1), (33633499, 1)] : List FactorBlock).map factorBlockValue).prod) = 9679721012201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_1439
      · exact prime_oneHundredSixtyThreeFE_33633499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 9679721012201) ^ 4839860506100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9679721012201) ^ 1935944202440 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9679721012201) ^ 6726699800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 9679721012201) ^ 287800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_9818399872903 : Nat.Prime 9818399872903 := by
  apply lucas_primality 9818399872903 (5 : ZMod 9818399872903)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (179, 1), (1657, 1), (5517139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (179, 1), (1657, 1), (5517139, 1)] : List FactorBlock).map factorBlockValue).prod) = 9818399872903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_179
      · exact prime_oneHundredSixtyThreeFE_1657
      · exact prime_oneHundredSixtyThreeFE_5517139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9818399872903) ^ 4909199936451 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9818399872903) ^ 3272799957634 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9818399872903) ^ 54851395938 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9818399872903) ^ 5925407286 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9818399872903) ^ 1779618 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10025093624939 : Nat.Prime 10025093624939 := by
  apply lucas_primality 10025093624939 (2 : ZMod 10025093624939)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (167891, 1), (4265137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (167891, 1), (4265137, 1)] : List FactorBlock).map factorBlockValue).prod) = 10025093624939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_167891
      · exact prime_oneHundredSixtyThreeFE_4265137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10025093624939) ^ 5012546812469 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10025093624939) ^ 1432156232134 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10025093624939) ^ 59711918 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10025093624939) ^ 2350474 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10313940058469 : Nat.Prime 10313940058469 := by
  apply lucas_primality 10313940058469 (2 : ZMod 10313940058469)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (12979, 1), (2721451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (12979, 1), (2721451, 1)] : List FactorBlock).map factorBlockValue).prod) = 10313940058469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_73
      · exact prime_oneHundredSixtyThreeFE_12979
      · exact prime_oneHundredSixtyThreeFE_2721451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10313940058469) ^ 5156970029234 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10313940058469) ^ 141286850116 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10313940058469) ^ 794663692 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10313940058469) ^ 3789868 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10678314013303 : Nat.Prime 10678314013303 := by
  apply lucas_primality 10678314013303 (5 : ZMod 10678314013303)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1087, 1), (125944307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1087, 1), (125944307, 1)] : List FactorBlock).map factorBlockValue).prod) = 10678314013303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_1087
      · exact prime_oneHundredSixtyThreeFE_125944307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10678314013303) ^ 5339157006651 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10678314013303) ^ 3559438004434 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10678314013303) ^ 821408770254 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10678314013303) ^ 9823655946 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 10678314013303) ^ 84786 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_12179518900123 : Nat.Prime 12179518900123 := by
  apply lucas_primality 12179518900123 (2 : ZMod 12179518900123)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (79, 1), (20177, 1), (181927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (79, 1), (20177, 1), (181927, 1)] : List FactorBlock).map factorBlockValue).prod) = 12179518900123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_79
      · exact prime_oneHundredSixtyThreeFE_20177
      · exact prime_oneHundredSixtyThreeFE_181927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12179518900123) ^ 6089759450061 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12179518900123) ^ 4059839633374 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12179518900123) ^ 1739931271446 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12179518900123) ^ 154171125318 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12179518900123) ^ 603633786 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12179518900123) ^ 66947286 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_12759971822261 : Nat.Prime 12759971822261 := by
  apply lucas_primality 12759971822261 (2 : ZMod 12759971822261)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (17, 1), (4817, 1), (599309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (17, 1), (4817, 1), (599309, 1)] : List FactorBlock).map factorBlockValue).prod) = 12759971822261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_4817
      · exact prime_oneHundredSixtyThreeFE_599309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12759971822261) ^ 6379985911130 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12759971822261) ^ 2551994364452 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12759971822261) ^ 981536294020 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12759971822261) ^ 750586577780 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12759971822261) ^ 2648945780 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12759971822261) ^ 21291140 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_13764554738563 : Nat.Prime 13764554738563 := by
  apply lucas_primality 13764554738563 (2 : ZMod 13764554738563)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (557, 1), (587, 1), (9007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (557, 1), (587, 1), (9007, 1)] : List FactorBlock).map factorBlockValue).prod) = 13764554738563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_41
      · exact prime_oneHundredSixtyThreeFE_557
      · exact prime_oneHundredSixtyThreeFE_587
      · exact prime_oneHundredSixtyThreeFE_9007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13764554738563) ^ 6882277369281 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 4588184912854 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 724450249398 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 335720847282 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 24711947466 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 23448985926 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 13764554738563) ^ 1528206366 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_25151428502917 : Nat.Prime 25151428502917 := by
  apply lucas_primality 25151428502917 (2 : ZMod 25151428502917)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (53, 1), (28351, 1), (60647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (53, 1), (28351, 1), (60647, 1)] : List FactorBlock).map factorBlockValue).prod) = 25151428502917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_53
      · exact prime_oneHundredSixtyThreeFE_28351
      · exact prime_oneHundredSixtyThreeFE_60647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25151428502917) ^ 12575714251458 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25151428502917) ^ 8383809500972 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25151428502917) ^ 1093540369692 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25151428502917) ^ 474555254772 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25151428502917) ^ 887144316 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 25151428502917) ^ 414718428 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_51516113893919 : Nat.Prime 51516113893919 := by
  apply lucas_primality 51516113893919 (11 : ZMod 51516113893919)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (157, 1), (2801, 1), (2546669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (157, 1), (2801, 1), (2546669, 1)] : List FactorBlock).map factorBlockValue).prod) = 51516113893919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_157
      · exact prime_oneHundredSixtyThreeFE_2801
      · exact prime_oneHundredSixtyThreeFE_2546669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 51516113893919) ^ 25758056946959 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 51516113893919) ^ 2239831038866 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 51516113893919) ^ 328128113974 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 51516113893919) ^ 18392043518 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 51516113893919) ^ 20228822 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_89373875307361 : Nat.Prime 89373875307361 := by
  apply lucas_primality 89373875307361 (19 : ZMod 89373875307361)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (71, 1), (6547, 1), (57223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (71, 1), (6547, 1), (57223, 1)] : List FactorBlock).map factorBlockValue).prod) = 89373875307361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_71
      · exact prime_oneHundredSixtyThreeFE_6547
      · exact prime_oneHundredSixtyThreeFE_57223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 89373875307361) ^ 44686937653680 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 29791291769120 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 17874775061472 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 12767696472480 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 1258786976160 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 13651118880 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (19 : ZMod 89373875307361) ^ 1561852320 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_90868284865453 : Nat.Prime 90868284865453 := by
  apply lucas_primality 90868284865453 (2 : ZMod 90868284865453)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (398545109059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (398545109059, 1)] : List FactorBlock).map factorBlockValue).prod) = 90868284865453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_398545109059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 90868284865453) ^ 45434142432726 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90868284865453) ^ 30289428288484 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90868284865453) ^ 4782541308708 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90868284865453) ^ 228 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_94152153091831 : Nat.Prime 94152153091831 := by
  apply lucas_primality 94152153091831 (3 : ZMod 94152153091831)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3138405103061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3138405103061, 1)] : List FactorBlock).map factorBlockValue).prod) = 94152153091831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_3138405103061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 94152153091831) ^ 47076076545915 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94152153091831) ^ 31384051030610 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94152153091831) ^ 18830430618366 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94152153091831) ^ 30 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_106733160018971 : Nat.Prime 106733160018971 := by
  apply lucas_primality 106733160018971 (6 : ZMod 106733160018971)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (85303, 1), (125122399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (85303, 1), (125122399, 1)] : List FactorBlock).map factorBlockValue).prod) = 106733160018971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_85303
      · exact prime_oneHundredSixtyThreeFE_125122399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 106733160018971) ^ 53366580009485 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 106733160018971) ^ 21346632003794 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 106733160018971) ^ 1251223990 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 106733160018971) ^ 853030 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_177591121131113 : Nat.Prime 177591121131113 := by
  apply lucas_primality 177591121131113 (3 : ZMod 177591121131113)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (193, 1), (479, 1), (18471199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (193, 1), (479, 1), (18471199, 1)] : List FactorBlock).map factorBlockValue).prod) = 177591121131113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_193
      · exact prime_oneHundredSixtyThreeFE_479
      · exact prime_oneHundredSixtyThreeFE_18471199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 177591121131113) ^ 88795560565556 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177591121131113) ^ 13660855471624 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177591121131113) ^ 920161249384 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177591121131113) ^ 370753906328 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 177591121131113) ^ 9614488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_239350945294117 : Nat.Prime 239350945294117 := by
  apply lucas_primality 239350945294117 (7 : ZMod 239350945294117)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (293, 1), (313, 1), (457, 1), (52879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (293, 1), (313, 1), (457, 1), (52879, 1)] : List FactorBlock).map factorBlockValue).prod) = 239350945294117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_293
      · exact prime_oneHundredSixtyThreeFE_313
      · exact prime_oneHundredSixtyThreeFE_457
      · exact prime_oneHundredSixtyThreeFE_52879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 239350945294117) ^ 119675472647058 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 239350945294117) ^ 79783648431372 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 239350945294117) ^ 816897424212 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 239350945294117) ^ 764699505732 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 239350945294117) ^ 523743862788 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 239350945294117) ^ 4526389404 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_254840828248301 : Nat.Prime 254840828248301 := by
  apply lucas_primality 254840828248301 (2 : ZMod 254840828248301)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (163, 1), (2233486663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (163, 1), (2233486663, 1)] : List FactorBlock).map factorBlockValue).prod) = 254840828248301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_163
      · exact prime_oneHundredSixtyThreeFE_2233486663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 254840828248301) ^ 127420414124150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254840828248301) ^ 50968165649660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254840828248301) ^ 36405832606900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254840828248301) ^ 1563440664100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 254840828248301) ^ 114100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_283504413317233 : Nat.Prime 283504413317233 := by
  apply lucas_primality 283504413317233 (5 : ZMod 283504413317233)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (433, 1), (13640512573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (433, 1), (13640512573, 1)] : List FactorBlock).map factorBlockValue).prod) = 283504413317233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_433
      · exact prime_oneHundredSixtyThreeFE_13640512573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 283504413317233) ^ 141752206658616 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 283504413317233) ^ 94501471105744 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 283504413317233) ^ 654744603504 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 283504413317233) ^ 20784 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_332100232058599 : Nat.Prime 332100232058599 := by
  apply lucas_primality 332100232058599 (3 : ZMod 332100232058599)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (337, 1), (164243438209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (337, 1), (164243438209, 1)] : List FactorBlock).map factorBlockValue).prod) = 332100232058599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_337
      · exact prime_oneHundredSixtyThreeFE_164243438209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 332100232058599) ^ 166050116029299 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 332100232058599) ^ 110700077352866 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 332100232058599) ^ 985460629254 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 332100232058599) ^ 2022 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_396013744414319 : Nat.Prime 396013744414319 := by
  apply lucas_primality 396013744414319 (11 : ZMod 396013744414319)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (349, 1), (383, 1), (14666777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (349, 1), (383, 1), (14666777, 1)] : List FactorBlock).map factorBlockValue).prod) = 396013744414319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_101
      · exact prime_oneHundredSixtyThreeFE_349
      · exact prime_oneHundredSixtyThreeFE_383
      · exact prime_oneHundredSixtyThreeFE_14666777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 396013744414319) ^ 198006872207159 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 396013744414319) ^ 3920928162518 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 396013744414319) ^ 1134709869382 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 396013744414319) ^ 1033978444946 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 396013744414319) ^ 27000734 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_918717971202793 : Nat.Prime 918717971202793 := by
  apply lucas_primality 918717971202793 (5 : ZMod 918717971202793)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (12759971822261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (12759971822261, 1)] : List FactorBlock).map factorBlockValue).prod) = 918717971202793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_12759971822261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 918717971202793) ^ 459358985601396 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 918717971202793) ^ 306239323734264 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 918717971202793) ^ 72 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1011444789871237 : Nat.Prime 1011444789871237 := by
  apply lucas_primality 1011444789871237 (2 : ZMod 1011444789871237)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (29, 1), (31477, 1), (13190813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (29, 1), (31477, 1), (13190813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1011444789871237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_31477
      · exact prime_oneHundredSixtyThreeFE_13190813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1011444789871237) ^ 505722394935618 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011444789871237) ^ 337148263290412 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011444789871237) ^ 144492112838748 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011444789871237) ^ 34877406547284 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011444789871237) ^ 32132820468 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1011444789871237) ^ 76677972 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2134663200379421 : Nat.Prime 2134663200379421 := by
  apply lucas_primality 2134663200379421 (2 : ZMod 2134663200379421)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (106733160018971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (106733160018971, 1)] : List FactorBlock).map factorBlockValue).prod) = 2134663200379421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_106733160018971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2134663200379421) ^ 1067331600189710 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134663200379421) ^ 426932640075884 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2134663200379421) ^ 20 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2536315156044419 : Nat.Prime 2536315156044419 := by
  apply lucas_primality 2536315156044419 (2 : ZMod 2536315156044419)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (83, 1), (2182715280589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (83, 1), (2182715280589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2536315156044419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_83
      · exact prime_oneHundredSixtyThreeFE_2182715280589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2536315156044419) ^ 1268157578022209 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2536315156044419) ^ 362330736577774 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2536315156044419) ^ 30558013928246 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2536315156044419) ^ 1162 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2636260286571269 : Nat.Prime 2636260286571269 := by
  apply lucas_primality 2636260286571269 (2 : ZMod 2636260286571269)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (94152153091831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (94152153091831, 1)] : List FactorBlock).map factorBlockValue).prod) = 2636260286571269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_94152153091831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2636260286571269) ^ 1318130143285634 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2636260286571269) ^ 376608612367324 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2636260286571269) ^ 28 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2752972414571273 : Nat.Prime 2752972414571273 := by
  apply lucas_primality 2752972414571273 (3 : ZMod 2752972414571273)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (324763, 1), (1059608243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (324763, 1), (1059608243, 1)] : List FactorBlock).map factorBlockValue).prod) = 2752972414571273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_324763
      · exact prime_oneHundredSixtyThreeFE_1059608243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2752972414571273) ^ 1376486207285636 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752972414571273) ^ 8476865944 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2752972414571273) ^ 2598104 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3202538555710673 : Nat.Prime 3202538555710673 := by
  apply lucas_primality 3202538555710673 (3 : ZMod 3202538555710673)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (89, 1), (631, 1), (857, 1), (4158859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (89, 1), (631, 1), (857, 1), (4158859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3202538555710673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_89
      · exact prime_oneHundredSixtyThreeFE_631
      · exact prime_oneHundredSixtyThreeFE_857
      · exact prime_oneHundredSixtyThreeFE_4158859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3202538555710673) ^ 1601269277855336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3202538555710673) ^ 35983579277648 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3202538555710673) ^ 5075338440112 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3202538555710673) ^ 3736917801296 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3202538555710673) ^ 770052208 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3798889829124463 : Nat.Prime 3798889829124463 := by
  apply lucas_primality 3798889829124463 (3 : ZMod 3798889829124463)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (211, 1), (6290781691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (211, 1), (6290781691, 1)] : List FactorBlock).map factorBlockValue).prod) = 3798889829124463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_53
      · exact prime_oneHundredSixtyThreeFE_211
      · exact prime_oneHundredSixtyThreeFE_6290781691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3798889829124463) ^ 1899444914562231 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3798889829124463) ^ 1266296609708154 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3798889829124463) ^ 71677166587254 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3798889829124463) ^ 18004217199642 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3798889829124463) ^ 603882 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5163029679054529 : Nat.Prime 5163029679054529 := by
  apply lucas_primality 5163029679054529 (11 : ZMod 5163029679054529)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (163, 1), (18330456427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (163, 1), (18330456427, 1)] : List FactorBlock).map factorBlockValue).prod) = 5163029679054529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_163
      · exact prime_oneHundredSixtyThreeFE_18330456427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 5163029679054529) ^ 2581514839527264 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5163029679054529) ^ 1721009893018176 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5163029679054529) ^ 31675028705856 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 5163029679054529) ^ 281664 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_5845849187225947 : Nat.Prime 5845849187225947 := by
  apply lucas_primality 5845849187225947 (2 : ZMod 5845849187225947)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (112543, 1), (8657208337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (112543, 1), (8657208337, 1)] : List FactorBlock).map factorBlockValue).prod) = 5845849187225947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_112543
      · exact prime_oneHundredSixtyThreeFE_8657208337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5845849187225947) ^ 2922924593612973 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5845849187225947) ^ 1948616395741982 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5845849187225947) ^ 51943250022 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5845849187225947) ^ 675258 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6494991232212649 : Nat.Prime 6494991232212649 := by
  apply lucas_primality 6494991232212649 (7 : ZMod 6494991232212649)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (31, 1), (13829, 1), (19129381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (31, 1), (13829, 1), (19129381, 1)] : List FactorBlock).map factorBlockValue).prod) = 6494991232212649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_31
      · exact prime_oneHundredSixtyThreeFE_13829
      · exact prime_oneHundredSixtyThreeFE_19129381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6494991232212649) ^ 3247495616106324 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6494991232212649) ^ 2164997077404216 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6494991232212649) ^ 590453748382968 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6494991232212649) ^ 209515846200408 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6494991232212649) ^ 469664562312 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6494991232212649) ^ 339529608 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8144153412524599 : Nat.Prime 8144153412524599 := by
  apply lucas_primality 8144153412524599 (3 : ZMod 8144153412524599)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (599, 1), (809, 1), (57164087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (599, 1), (809, 1), (57164087, 1)] : List FactorBlock).map factorBlockValue).prod) = 8144153412524599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_599
      · exact prime_oneHundredSixtyThreeFE_809
      · exact prime_oneHundredSixtyThreeFE_57164087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8144153412524599) ^ 4072076706262299 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8144153412524599) ^ 2714717804174866 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8144153412524599) ^ 1163450487503514 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8144153412524599) ^ 13596249436602 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8144153412524599) ^ 10066938705222 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8144153412524599) ^ 142469754 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_14344668081391313 : Nat.Prime 14344668081391313 := by
  apply lucas_primality 14344668081391313 (3 : ZMod 14344668081391313)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (29, 1), (1367, 1), (39509, 1), (81773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (29, 1), (1367, 1), (39509, 1), (81773, 1)] : List FactorBlock).map factorBlockValue).prod) = 14344668081391313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_1367
      · exact prime_oneHundredSixtyThreeFE_39509
      · exact prime_oneHundredSixtyThreeFE_81773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14344668081391313) ^ 7172334040695656 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344668081391313) ^ 2049238297341616 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344668081391313) ^ 494643726944528 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344668081391313) ^ 10493539196336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344668081391313) ^ 363073428368 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14344668081391313) ^ 175420592144 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_16990454495024429 : Nat.Prime 16990454495024429 := by
  apply lucas_primality 16990454495024429 (2 : ZMod 16990454495024429)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (73, 1), (5289680726969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (73, 1), (5289680726969, 1)] : List FactorBlock).map factorBlockValue).prod) = 16990454495024429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_73
      · exact prime_oneHundredSixtyThreeFE_5289680726969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 16990454495024429) ^ 8495227247512214 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990454495024429) ^ 1544586772274948 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990454495024429) ^ 232745951986636 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16990454495024429) ^ 3212 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_24417029884333907 : Nat.Prime 24417029884333907 := by
  apply lucas_primality 24417029884333907 (2 : ZMod 24417029884333907)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (83, 1), (7741607445889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (83, 1), (7741607445889, 1)] : List FactorBlock).map factorBlockValue).prod) = 24417029884333907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_83
      · exact prime_oneHundredSixtyThreeFE_7741607445889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24417029884333907) ^ 12208514942166953 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24417029884333907) ^ 1285106836017574 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24417029884333907) ^ 294181082943782 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 24417029884333907) ^ 3154 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_26340005596089943 : Nat.Prime 26340005596089943 := by
  apply lucas_primality 26340005596089943 (3 : ZMod 26340005596089943)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (37, 1), (1753, 1), (7307, 1), (1029199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (37, 1), (1753, 1), (7307, 1), (1029199, 1)] : List FactorBlock).map factorBlockValue).prod) = 26340005596089943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_1753
      · exact prime_oneHundredSixtyThreeFE_7307
      · exact prime_oneHundredSixtyThreeFE_1029199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 26340005596089943) ^ 13170002798044971 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26340005596089943) ^ 8780001865363314 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26340005596089943) ^ 711892043137566 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26340005596089943) ^ 15025673471814 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26340005596089943) ^ 3604763322306 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 26340005596089943) ^ 25592723658 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_27191214674521141 : Nat.Prime 27191214674521141 := by
  apply lucas_primality 27191214674521141 (7 : ZMod 27191214674521141)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (47, 1), (419229335099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (47, 1), (419229335099, 1)] : List FactorBlock).map factorBlockValue).prod) = 27191214674521141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_419229335099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 27191214674521141) ^ 13595607337260570 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 27191214674521141) ^ 9063738224840380 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 27191214674521141) ^ 5438242934904228 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 27191214674521141) ^ 1182226724979180 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 27191214674521141) ^ 578536482436620 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 27191214674521141) ^ 64860 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_27944084630306567 : Nat.Prime 27944084630306567 := by
  apply lucas_primality 27944084630306567 (5 : ZMod 27944084630306567)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (106669, 1), (182389, 1), (718163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (106669, 1), (182389, 1), (718163, 1)] : List FactorBlock).map factorBlockValue).prod) = 27944084630306567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_106669
      · exact prime_oneHundredSixtyThreeFE_182389
      · exact prime_oneHundredSixtyThreeFE_718163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27944084630306567) ^ 13972042315153283 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27944084630306567) ^ 261970062814 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27944084630306567) ^ 153211458094 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27944084630306567) ^ 38910504482 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_28689336162782627 : Nat.Prime 28689336162782627 := by
  apply lucas_primality 28689336162782627 (2 : ZMod 28689336162782627)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14344668081391313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14344668081391313, 1)] : List FactorBlock).map factorBlockValue).prod) = 28689336162782627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_14344668081391313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28689336162782627) ^ 14344668081391313 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28689336162782627) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_46320057817430119 : Nat.Prime 46320057817430119 := by
  apply lucas_primality 46320057817430119 (3 : ZMod 46320057817430119)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (97187, 1), (1937429059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (97187, 1), (1937429059, 1)] : List FactorBlock).map factorBlockValue).prod) = 46320057817430119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_41
      · exact prime_oneHundredSixtyThreeFE_97187
      · exact prime_oneHundredSixtyThreeFE_1937429059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46320057817430119) ^ 23160028908715059 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46320057817430119) ^ 15440019272476706 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46320057817430119) ^ 1129757507742198 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46320057817430119) ^ 476607548514 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 46320057817430119) ^ 23908002 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_69963126446776663 : Nat.Prime 69963126446776663 := by
  apply lucas_primality 69963126446776663 (3 : ZMod 69963126446776663)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (83, 1), (4257218355043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (83, 1), (4257218355043, 1)] : List FactorBlock).map factorBlockValue).prod) = 69963126446776663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_83
      · exact prime_oneHundredSixtyThreeFE_4257218355043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69963126446776663) ^ 34981563223388331 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69963126446776663) ^ 23321042148925554 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69963126446776663) ^ 6360284222434242 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69963126446776663) ^ 842929234298514 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 69963126446776663) ^ 16434 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_92934534222981523 : Nat.Prime 92934534222981523 := by
  apply lucas_primality 92934534222981523 (2 : ZMod 92934534222981523)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5163029679054529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5163029679054529, 1)] : List FactorBlock).map factorBlockValue).prod) = 92934534222981523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5163029679054529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 92934534222981523) ^ 46467267111490761 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 92934534222981523) ^ 30978178074327174 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 92934534222981523) ^ 18 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_94195225462005487 : Nat.Prime 94195225462005487 := by
  apply lucas_primality 94195225462005487 (3 : ZMod 94195225462005487)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (1531, 1), (64217, 1), (584911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (1531, 1), (64217, 1), (584911, 1)] : List FactorBlock).map factorBlockValue).prod) = 94195225462005487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_1531
      · exact prime_oneHundredSixtyThreeFE_64217
      · exact prime_oneHundredSixtyThreeFE_584911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 94195225462005487) ^ 47097612731002743 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 31398408487335162 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 13456460780286498 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 7245786574000422 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 61525294227306 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 1466826937758 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 94195225462005487) ^ 161041979826 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_106531750254190013 : Nat.Prime 106531750254190013 := by
  apply lucas_primality 106531750254190013 (2 : ZMod 106531750254190013)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (29, 1), (32099, 1), (1243946591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (29, 1), (32099, 1), (1243946591, 1)] : List FactorBlock).map factorBlockValue).prod) = 106531750254190013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_32099
      · exact prime_oneHundredSixtyThreeFE_1243946591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106531750254190013) ^ 53265875127095006 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 106531750254190013) ^ 4631815228443044 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 106531750254190013) ^ 3673508629454828 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 106531750254190013) ^ 3318849504788 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 106531750254190013) ^ 85640132 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_115679467739794577 : Nat.Prime 115679467739794577 := by
  apply lucas_primality 115679467739794577 (3 : ZMod 115679467739794577)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (577, 1), (1699, 1), (1789, 1), (1951, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (577, 1), (1699, 1), (1789, 1), (1951, 1), (2113, 1)] : List FactorBlock).map factorBlockValue).prod) = 115679467739794577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_577
      · exact prime_oneHundredSixtyThreeFE_1699
      · exact prime_oneHundredSixtyThreeFE_1789
      · exact prime_oneHundredSixtyThreeFE_1951
      · exact prime_oneHundredSixtyThreeFE_2113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 115679467739794577) ^ 57839733869897288 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115679467739794577) ^ 200484346169488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115679467739794577) ^ 68086796786224 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115679467739794577) ^ 64661524728784 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115679467739794577) ^ 59292397611376 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 115679467739794577) ^ 54746553591952 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_156338458647727427 : Nat.Prime 156338458647727427 := by
  apply lucas_primality 156338458647727427 (2 : ZMod 156338458647727427)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13127, 1), (52861, 1), (16092997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13127, 1), (52861, 1), (16092997, 1)] : List FactorBlock).map factorBlockValue).prod) = 156338458647727427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_13127
      · exact prime_oneHundredSixtyThreeFE_52861
      · exact prime_oneHundredSixtyThreeFE_16092997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 156338458647727427) ^ 78169229323863713 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156338458647727427) ^ 22334065521103918 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156338458647727427) ^ 11909686801838 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156338458647727427) ^ 2957538802666 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 156338458647727427) ^ 9714688858 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_161806724685557183 : Nat.Prime 161806724685557183 := by
  apply lucas_primality 161806724685557183 (5 : ZMod 161806724685557183)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (20553583, 1), (51119701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (20553583, 1), (51119701, 1)] : List FactorBlock).map factorBlockValue).prod) = 161806724685557183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_20553583
      · exact prime_oneHundredSixtyThreeFE_51119701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 161806724685557183) ^ 80903362342778591 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 161806724685557183) ^ 23115246383651026 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 161806724685557183) ^ 14709702244141562 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 161806724685557183) ^ 7872433954 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 161806724685557183) ^ 3165251782 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_171441516148592489 : Nat.Prime 171441516148592489 := by
  apply lucas_primality 171441516148592489 (3 : ZMod 171441516148592489)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (8147, 1), (154731727439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (8147, 1), (154731727439, 1)] : List FactorBlock).map factorBlockValue).prod) = 171441516148592489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_8147
      · exact prime_oneHundredSixtyThreeFE_154731727439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 171441516148592489) ^ 85720758074296244 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 171441516148592489) ^ 10084795067564264 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 171441516148592489) ^ 21043514931704 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 171441516148592489) ^ 1107992 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_184826091416331403 : Nat.Prime 184826091416331403 := by
  apply lucas_primality 184826091416331403 (3 : ZMod 184826091416331403)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (113, 1), (90868284865453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (113, 1), (90868284865453, 1)] : List FactorBlock).map factorBlockValue).prod) = 184826091416331403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_113
      · exact prime_oneHundredSixtyThreeFE_90868284865453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 184826091416331403) ^ 92413045708165701 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 184826091416331403) ^ 61608697138777134 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 184826091416331403) ^ 1635629127578154 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 184826091416331403) ^ 2034 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_312453938988510829 : Nat.Prime 312453938988510829 := by
  apply lucas_primality 312453938988510829 (2 : ZMod 312453938988510829)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1433, 1), (1076323, 1), (16881691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1433, 1), (1076323, 1), (16881691, 1)] : List FactorBlock).map factorBlockValue).prod) = 312453938988510829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_1433
      · exact prime_oneHundredSixtyThreeFE_1076323
      · exact prime_oneHundredSixtyThreeFE_16881691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 312453938988510829) ^ 156226969494255414 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312453938988510829) ^ 104151312996170276 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312453938988510829) ^ 218041827626316 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312453938988510829) ^ 290297558436 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 312453938988510829) ^ 18508450308 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_321621611504589173 : Nat.Prime 321621611504589173 := by
  apply lucas_primality 321621611504589173 (2 : ZMod 321621611504589173)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (3766577, 1), (3049582187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (3766577, 1), (3049582187, 1)] : List FactorBlock).map factorBlockValue).prod) = 321621611504589173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_3766577
      · exact prime_oneHundredSixtyThreeFE_3049582187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 321621611504589173) ^ 160810805752294586 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321621611504589173) ^ 45945944500655596 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321621611504589173) ^ 85388301236 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321621611504589173) ^ 105464156 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_437999158137460009 : Nat.Prime 437999158137460009 := by
  apply lucas_primality 437999158137460009 (7 : ZMod 437999158137460009)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (59, 1), (7351, 1), (2214674977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (59, 1), (7351, 1), (2214674977, 1)] : List FactorBlock).map factorBlockValue).prod) = 437999158137460009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_59
      · exact prime_oneHundredSixtyThreeFE_7351
      · exact prime_oneHundredSixtyThreeFE_2214674977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 437999158137460009) ^ 218999579068730004 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 437999158137460009) ^ 145999719379153336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 437999158137460009) ^ 23052587270392632 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 437999158137460009) ^ 7423714544702712 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 437999158137460009) ^ 59583615581208 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 437999158137460009) ^ 197771304 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_627185508719753143 : Nat.Prime 627185508719753143 := by
  apply lucas_primality 627185508719753143 (3 : ZMod 627185508719753143)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (49360067, 1), (705907457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (49360067, 1), (705907457, 1)] : List FactorBlock).map factorBlockValue).prod) = 627185508719753143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_49360067
      · exact prime_oneHundredSixtyThreeFE_705907457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 627185508719753143) ^ 313592754359876571 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 627185508719753143) ^ 209061836239917714 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 627185508719753143) ^ 12706334226 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 627185508719753143) ^ 888481206 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_761869999798993243 : Nat.Prime 761869999798993243 := by
  apply lucas_primality 761869999798993243 (2 : ZMod 761869999798993243)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (181, 1), (6320159937277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (181, 1), (6320159937277, 1)] : List FactorBlock).map factorBlockValue).prod) = 761869999798993243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_181
      · exact prime_oneHundredSixtyThreeFE_6320159937277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 761869999798993243) ^ 380934999899496621 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 761869999798993243) ^ 253956666599664414 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 761869999798993243) ^ 20591081075648466 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 761869999798993243) ^ 4209226518226482 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 761869999798993243) ^ 120546 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1408037757789001063 : Nat.Prime 1408037757789001063 := by
  apply lucas_primality 1408037757789001063 (5 : ZMod 1408037757789001063)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12457, 1), (3463069, 1), (5439869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12457, 1), (3463069, 1), (5439869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1408037757789001063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_12457
      · exact prime_oneHundredSixtyThreeFE_3463069
      · exact prime_oneHundredSixtyThreeFE_5439869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1408037757789001063) ^ 704018878894500531 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408037757789001063) ^ 469345919263000354 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408037757789001063) ^ 113031850187766 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408037757789001063) ^ 406586688798 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1408037757789001063) ^ 258836703198 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1639171506015686701 : Nat.Prime 1639171506015686701 := by
  apply lucas_primality 1639171506015686701 (2 : ZMod 1639171506015686701)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (4294559, 1), (424095157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (4294559, 1), (424095157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1639171506015686701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_4294559
      · exact prime_oneHundredSixtyThreeFE_424095157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1639171506015686701) ^ 819585753007843350 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639171506015686701) ^ 546390502005228900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639171506015686701) ^ 327834301203137340 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639171506015686701) ^ 381685641300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1639171506015686701) ^ 3865103100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1758827077291164911 : Nat.Prime 1758827077291164911 := by
  apply lucas_primality 1758827077291164911 (7 : ZMod 1758827077291164911)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2554171, 1), (68860975921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2554171, 1), (68860975921, 1)] : List FactorBlock).map factorBlockValue).prod) = 1758827077291164911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_2554171
      · exact prime_oneHundredSixtyThreeFE_68860975921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1758827077291164911) ^ 879413538645582455 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1758827077291164911) ^ 351765415458232982 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1758827077291164911) ^ 688609759210 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1758827077291164911) ^ 25541710 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1882204938102400651 : Nat.Prime 1882204938102400651 := by
  apply lucas_primality 1882204938102400651 (2 : ZMod 1882204938102400651)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (127, 1), (2656427, 1), (12398033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (127, 1), (2656427, 1), (12398033, 1)] : List FactorBlock).map factorBlockValue).prod) = 1882204938102400651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_127
      · exact prime_oneHundredSixtyThreeFE_2656427
      · exact prime_oneHundredSixtyThreeFE_12398033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1882204938102400651) ^ 941102469051200325 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1882204938102400651) ^ 627401646034133550 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1882204938102400651) ^ 376440987620480130 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1882204938102400651) ^ 14820511323640950 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1882204938102400651) ^ 708547585950 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1882204938102400651) ^ 151814803050 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3269527157676699001 : Nat.Prime 3269527157676699001 := by
  apply lucas_primality 3269527157676699001 (7 : ZMod 3269527157676699001)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 3), (37, 1), (9818399872903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 3), (37, 1), (9818399872903, 1)] : List FactorBlock).map factorBlockValue).prod) = 3269527157676699001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_9818399872903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3269527157676699001) ^ 1634763578838349500 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3269527157676699001) ^ 1089842385892233000 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3269527157676699001) ^ 653905431535339800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3269527157676699001) ^ 88365598856127000 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 3269527157676699001) ^ 333000 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4837818333499727309 : Nat.Prime 4837818333499727309 := by
  apply lucas_primality 4837818333499727309 (2 : ZMod 4837818333499727309)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 2), (20828309, 1), (200926727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 2), (20828309, 1), (200926727, 1)] : List FactorBlock).map factorBlockValue).prod) = 4837818333499727309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_20828309
      · exact prime_oneHundredSixtyThreeFE_200926727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4837818333499727309) ^ 2418909166749863654 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4837818333499727309) ^ 284577549029395724 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4837818333499727309) ^ 232271296412 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4837818333499727309) ^ 24077525204 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7204486517949553601 : Nat.Prime 7204486517949553601 := by
  apply lucas_primality 7204486517949553601 (3 : ZMod 7204486517949553601)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (16243897, 1), (277199743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (16243897, 1), (277199743, 1)] : List FactorBlock).map factorBlockValue).prod) = 7204486517949553601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_16243897
      · exact prime_oneHundredSixtyThreeFE_277199743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7204486517949553601) ^ 3602243258974776800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7204486517949553601) ^ 1440897303589910720 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7204486517949553601) ^ 443519588800 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7204486517949553601) ^ 25990235200 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7778842196081819851 : Nat.Prime 7778842196081819851 := by
  apply lucas_primality 7778842196081819851 (2 : ZMod 7778842196081819851)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (13, 1), (23, 1), (3319, 1), (17419031593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (13, 1), (23, 1), (3319, 1), (17419031593, 1)] : List FactorBlock).map factorBlockValue).prod) = 7778842196081819851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_3319
      · exact prime_oneHundredSixtyThreeFE_17419031593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7778842196081819851) ^ 3889421098040909925 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 2592947398693939950 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 1555768439216363970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 598372476621678450 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 338210530264426950 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 2343730700838150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7778842196081819851) ^ 446571450 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8083541470050947231 : Nat.Prime 8083541470050947231 := by
  apply lucas_primality 8083541470050947231 (7 : ZMod 8083541470050947231)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (1724033, 1), (42624903721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (1724033, 1), (42624903721, 1)] : List FactorBlock).map factorBlockValue).prod) = 8083541470050947231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_1724033
      · exact prime_oneHundredSixtyThreeFE_42624903721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8083541470050947231) ^ 4041770735025473615 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8083541470050947231) ^ 1616708294010189446 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8083541470050947231) ^ 734867406368267930 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8083541470050947231) ^ 4688739409310 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 8083541470050947231) ^ 189643630 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_11443556418146214977 : Nat.Prime 11443556418146214977 := by
  apply lucas_primality 11443556418146214977 (3 : ZMod 11443556418146214977)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (19, 1), (119617, 1), (78674598283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (19, 1), (119617, 1), (78674598283, 1)] : List FactorBlock).map factorBlockValue).prod) = 11443556418146214977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_119617
      · exact prime_oneHundredSixtyThreeFE_78674598283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11443556418146214977) ^ 5721778209073107488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11443556418146214977) ^ 602292443060327104 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11443556418146214977) ^ 95668311512128 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11443556418146214977) ^ 145454272 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_18684733143587229347 : Nat.Prime 18684733143587229347 := by
  apply lucas_primality 18684733143587229347 (2 : ZMod 18684733143587229347)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 2), (409, 1), (3659985909017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 2), (409, 1), (3659985909017, 1)] : List FactorBlock).map factorBlockValue).prod) = 18684733143587229347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_79
      · exact prime_oneHundredSixtyThreeFE_409
      · exact prime_oneHundredSixtyThreeFE_3659985909017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18684733143587229347) ^ 9342366571793614673 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18684733143587229347) ^ 236515609412496574 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18684733143587229347) ^ 45683944116350194 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 18684733143587229347) ^ 5105138 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_30012579737124748651 : Nat.Prime 30012579737124748651 := by
  apply lucas_primality 30012579737124748651 (10 : ZMod 30012579737124748651)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19993, 1), (39671, 1), (84089099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19993, 1), (39671, 1), (84089099, 1)] : List FactorBlock).map factorBlockValue).prod) = 30012579737124748651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_19993
      · exact prime_oneHundredSixtyThreeFE_39671
      · exact prime_oneHundredSixtyThreeFE_84089099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 30012579737124748651) ^ 15006289868562374325 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 30012579737124748651) ^ 10004193245708249550 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 30012579737124748651) ^ 6002515947424949730 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 30012579737124748651) ^ 1501154390893050 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 30012579737124748651) ^ 756537010338150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 30012579737124748651) ^ 356914036350 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_38750621203211786321 : Nat.Prime 38750621203211786321 := by
  apply lucas_primality 38750621203211786321 (6 : ZMod 38750621203211786321)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (180984247, 1), (2676380807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (180984247, 1), (2676380807, 1)] : List FactorBlock).map factorBlockValue).prod) = 38750621203211786321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_180984247
      · exact prime_oneHundredSixtyThreeFE_2676380807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 38750621203211786321) ^ 19375310601605893160 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38750621203211786321) ^ 7750124240642357264 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38750621203211786321) ^ 214110464560 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38750621203211786321) ^ 14478739760 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_48142860285829568057 : Nat.Prime 48142860285829568057 := by
  apply lucas_primality 48142860285829568057 (3 : ZMod 48142860285829568057)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (178781, 1), (4808642605621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (178781, 1), (4808642605621, 1)] : List FactorBlock).map factorBlockValue).prod) = 48142860285829568057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_178781
      · exact prime_oneHundredSixtyThreeFE_4808642605621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 48142860285829568057) ^ 24071430142914784028 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48142860285829568057) ^ 6877551469404224008 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48142860285829568057) ^ 269283985914776 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 48142860285829568057) ^ 10011736 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_65325494198440466317 : Nat.Prime 65325494198440466317 := by
  apply lucas_primality 65325494198440466317 (2 : ZMod 65325494198440466317)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (3527, 1), (451051, 1), (1140641303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (3527, 1), (451051, 1), (1140641303, 1)] : List FactorBlock).map factorBlockValue).prod) = 65325494198440466317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_3527
      · exact prime_oneHundredSixtyThreeFE_451051
      · exact prime_oneHundredSixtyThreeFE_1140641303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65325494198440466317) ^ 32662747099220233158 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65325494198440466317) ^ 21775164732813488772 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65325494198440466317) ^ 18521546412940308 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65325494198440466317) ^ 144829507524516 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65325494198440466317) ^ 57270847572 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_77501242406423572643 : Nat.Prime 77501242406423572643 := by
  apply lucas_primality 77501242406423572643 (2 : ZMod 77501242406423572643)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (38750621203211786321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (38750621203211786321, 1)] : List FactorBlock).map factorBlockValue).prod) = 77501242406423572643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_38750621203211786321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 77501242406423572643) ^ 38750621203211786321 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77501242406423572643) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_77884491958079702473 : Nat.Prime 77884491958079702473 := by
  apply lucas_primality 77884491958079702473 (11 : ZMod 77884491958079702473)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (37, 1), (2729, 1), (930437, 1), (11514001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (37, 1), (2729, 1), (930437, 1), (11514001, 1)] : List FactorBlock).map factorBlockValue).prod) = 77884491958079702473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_2729
      · exact prime_oneHundredSixtyThreeFE_930437
      · exact prime_oneHundredSixtyThreeFE_11514001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 77884491958079702473) ^ 38942245979039851236 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 77884491958079702473) ^ 25961497319359900824 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 77884491958079702473) ^ 2104986269137289256 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 77884491958079702473) ^ 28539571989036168 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 77884491958079702473) ^ 83707432054056 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 77884491958079702473) ^ 6764329094472 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_78358701620389862561 : Nat.Prime 78358701620389862561 := by
  apply lucas_primality 78358701620389862561 (3 : ZMod 78358701620389862561)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (69963126446776663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (69963126446776663, 1)] : List FactorBlock).map factorBlockValue).prod) = 78358701620389862561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_69963126446776663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 78358701620389862561) ^ 39179350810194931280 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 78358701620389862561) ^ 15671740324077972512 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 78358701620389862561) ^ 11194100231484266080 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 78358701620389862561) ^ 1120 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_83654065572201457799 : Nat.Prime 83654065572201457799 := by
  apply lucas_primality 83654065572201457799 (7 : ZMod 83654065572201457799)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1601, 1), (2699, 1), (9679721012201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1601, 1), (2699, 1), (9679721012201, 1)] : List FactorBlock).map factorBlockValue).prod) = 83654065572201457799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_1601
      · exact prime_oneHundredSixtyThreeFE_2699
      · exact prime_oneHundredSixtyThreeFE_9679721012201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 83654065572201457799) ^ 41827032786100728899 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 83654065572201457799) ^ 52251134023860998 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 83654065572201457799) ^ 30994466681067602 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 83654065572201457799) ^ 8642198 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_167308131144402915599 : Nat.Prime 167308131144402915599 := by
  apply lucas_primality 167308131144402915599 (7 : ZMod 167308131144402915599)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83654065572201457799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83654065572201457799, 1)] : List FactorBlock).map factorBlockValue).prod) = 167308131144402915599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_83654065572201457799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 167308131144402915599) ^ 83654065572201457799 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 167308131144402915599) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_222580933818977582753 : Nat.Prime 222580933818977582753 := by
  apply lucas_primality 222580933818977582753 (3 : ZMod 222580933818977582753)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (135019, 1), (51516113893919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (135019, 1), (51516113893919, 1)] : List FactorBlock).map factorBlockValue).prod) = 222580933818977582753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_135019
      · exact prime_oneHundredSixtyThreeFE_51516113893919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 222580933818977582753) ^ 111290466909488791376 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 222580933818977582753) ^ 1648515644605408 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 222580933818977582753) ^ 4320608 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_317226767671978832033 : Nat.Prime 317226767671978832033 := by
  apply lucas_primality 317226767671978832033 (3 : ZMod 317226767671978832033)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (127, 1), (18138509, 1), (4303428007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (127, 1), (18138509, 1), (4303428007, 1)] : List FactorBlock).map factorBlockValue).prod) = 317226767671978832033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_127
      · exact prime_oneHundredSixtyThreeFE_18138509
      · exact prime_oneHundredSixtyThreeFE_4303428007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 317226767671978832033) ^ 158613383835989416016 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 317226767671978832033) ^ 2497848564346290016 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 317226767671978832033) ^ 17489131420448 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 317226767671978832033) ^ 73714900576 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_334616262288805831199 : Nat.Prime 334616262288805831199 := by
  apply lucas_primality 334616262288805831199 (13 : ZMod 334616262288805831199)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167308131144402915599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167308131144402915599, 1)] : List FactorBlock).map factorBlockValue).prod) = 334616262288805831199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_167308131144402915599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 334616262288805831199) ^ 167308131144402915599 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (13 : ZMod 334616262288805831199) ^ 2 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_379622917713639092567 : Nat.Prime 379622917713639092567 := by
  apply lucas_primality 379622917713639092567 (5 : ZMod 379622917713639092567)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (6569, 1), (84239, 1), (18053290127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (6569, 1), (84239, 1), (18053290127, 1)] : List FactorBlock).map factorBlockValue).prod) = 379622917713639092567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_6569
      · exact prime_oneHundredSixtyThreeFE_84239
      · exact prime_oneHundredSixtyThreeFE_18053290127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 379622917713639092567) ^ 189811458856819546283 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 379622917713639092567) ^ 19980153563875741714 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 379622917713639092567) ^ 57790062066317414 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 379622917713639092567) ^ 4506498388081994 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 379622917713639092567) ^ 21027907658 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_509467116610384709087 : Nat.Prime 509467116610384709087 := by
  apply lucas_primality 509467116610384709087 (5 : ZMod 509467116610384709087)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2741, 1), (92934534222981523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2741, 1), (92934534222981523, 1)] : List FactorBlock).map factorBlockValue).prod) = 509467116610384709087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_2741
      · exact prime_oneHundredSixtyThreeFE_92934534222981523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 509467116610384709087) ^ 254733558305192354543 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 509467116610384709087) ^ 185869068445963046 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 509467116610384709087) ^ 5482 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_511733407669262404463 : Nat.Prime 511733407669262404463 := by
  apply lucas_primality 511733407669262404463 (5 : ZMod 511733407669262404463)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (227, 1), (147328583, 1), (263817079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (227, 1), (147328583, 1), (263817079, 1)] : List FactorBlock).map factorBlockValue).prod) = 511733407669262404463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_227
      · exact prime_oneHundredSixtyThreeFE_147328583
      · exact prime_oneHundredSixtyThreeFE_263817079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 511733407669262404463) ^ 255866703834631202231 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 511733407669262404463) ^ 17645979574802151878 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 511733407669262404463) ^ 2254332192375605306 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 511733407669262404463) ^ 3473415662114 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 511733407669262404463) ^ 1939728123778 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_656731939826732175467 : Nat.Prime 656731939826732175467 := by
  apply lucas_primality 656731939826732175467 (2 : ZMod 656731939826732175467)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (761869999798993243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (761869999798993243, 1)] : List FactorBlock).map factorBlockValue).prod) = 656731939826732175467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_431
      · exact prime_oneHundredSixtyThreeFE_761869999798993243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 656731939826732175467) ^ 328365969913366087733 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 656731939826732175467) ^ 1523739999597986486 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 656731939826732175467) ^ 862 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1185771661400283198301 : Nat.Prime 1185771661400283198301 := by
  apply lucas_primality 1185771661400283198301 (2 : ZMod 1185771661400283198301)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (2621, 1), (7392967, 1), (67994341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (2621, 1), (7392967, 1), (67994341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185771661400283198301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_2621
      · exact prime_oneHundredSixtyThreeFE_7392967
      · exact prime_oneHundredSixtyThreeFE_67994341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1185771661400283198301) ^ 592885830700141599150 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185771661400283198301) ^ 395257220466761066100 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185771661400283198301) ^ 237154332280056639660 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185771661400283198301) ^ 452411927279772300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185771661400283198301) ^ 160391850984900 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185771661400283198301) ^ 17439269856300 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_2546220167404863076189 : Nat.Prime 2546220167404863076189 := by
  apply lucas_primality 2546220167404863076189 (2 : ZMod 2546220167404863076189)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (61, 1), (271, 1), (525923, 1), (8135273591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (61, 1), (271, 1), (525923, 1), (8135273591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2546220167404863076189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_61
      · exact prime_oneHundredSixtyThreeFE_271
      · exact prime_oneHundredSixtyThreeFE_525923
      · exact prime_oneHundredSixtyThreeFE_8135273591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2546220167404863076189) ^ 1273110083702431538094 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2546220167404863076189) ^ 848740055801621025396 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2546220167404863076189) ^ 41741314219751853708 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2546220167404863076189) ^ 9395646374187686628 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2546220167404863076189) ^ 4841431478381556 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2546220167404863076189) ^ 312985192068 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6155185499543895317957 : Nat.Prime 6155185499543895317957 := by
  apply lucas_primality 6155185499543895317957 (2 : ZMod 6155185499543895317957)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (2161, 1), (2315881, 1), (5211444731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (2161, 1), (2315881, 1), (5211444731, 1)] : List FactorBlock).map factorBlockValue).prod) = 6155185499543895317957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_59
      · exact prime_oneHundredSixtyThreeFE_2161
      · exact prime_oneHundredSixtyThreeFE_2315881
      · exact prime_oneHundredSixtyThreeFE_5211444731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6155185499543895317957) ^ 3077592749771947658978 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6155185499543895317957) ^ 104325177958371107084 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6155185499543895317957) ^ 2848304257077230596 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6155185499543895317957) ^ 2657815967031076 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 6155185499543895317957) ^ 1181090046476 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7019028646705856035579 : Nat.Prime 7019028646705856035579 := by
  apply lucas_primality 7019028646705856035579 (3 : ZMod 7019028646705856035579)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (73, 1), (91033, 1), (7653784202809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (73, 1), (91033, 1), (7653784202809, 1)] : List FactorBlock).map factorBlockValue).prod) = 7019028646705856035579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_73
      · exact prime_oneHundredSixtyThreeFE_91033
      · exact prime_oneHundredSixtyThreeFE_7653784202809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7019028646705856035579) ^ 3509514323352928017789 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7019028646705856035579) ^ 2339676215568618678526 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7019028646705856035579) ^ 305175158552428523286 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7019028646705856035579) ^ 96151077352135014186 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7019028646705856035579) ^ 77104222059097866 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 7019028646705856035579) ^ 917066442 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7650693548963475662341 : Nat.Prime 7650693548963475662341 := by
  apply lucas_primality 7650693548963475662341 (10 : ZMod 7650693548963475662341)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (3269527157676699001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (3269527157676699001, 1)] : List FactorBlock).map factorBlockValue).prod) = 7650693548963475662341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_3269527157676699001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 7650693548963475662341) ^ 3825346774481737831170 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 7650693548963475662341) ^ 2550231182987825220780 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 7650693548963475662341) ^ 1530138709792695132468 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 7650693548963475662341) ^ 588514888381805820180 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 7650693548963475662341) ^ 2340 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_9731553762580584638293 : Nat.Prime 9731553762580584638293 := by
  apply lucas_primality 9731553762580584638293 (5 : ZMod 9731553762580584638293)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11071, 1), (24417029884333907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11071, 1), (24417029884333907, 1)] : List FactorBlock).map factorBlockValue).prod) = 9731553762580584638293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_11071
      · exact prime_oneHundredSixtyThreeFE_24417029884333907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9731553762580584638293) ^ 4865776881290292319146 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9731553762580584638293) ^ 3243851254193528212764 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9731553762580584638293) ^ 879013075836020652 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 9731553762580584638293) ^ 398556 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10346413936805375815591 : Nat.Prime 10346413936805375815591 := by
  apply lucas_primality 10346413936805375815591 (7 : ZMod 10346413936805375815591)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (47, 1), (53, 1), (8144153412524599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (47, 1), (53, 1), (8144153412524599, 1)] : List FactorBlock).map factorBlockValue).prod) = 10346413936805375815591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_47
      · exact prime_oneHundredSixtyThreeFE_53
      · exact prime_oneHundredSixtyThreeFE_8144153412524599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 10346413936805375815591) ^ 5173206968402687907795 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 3448804645601791938530 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 2069282787361075163118 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 608612584517963283270 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 220136466740539910970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 195215357298214638030 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 10346413936805375815591) ^ 1270410 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_12011728285836368416157 : Nat.Prime 12011728285836368416157 := by
  apply lucas_primality 12011728285836368416157 (2 : ZMod 12011728285836368416157)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (37, 1), (173, 1), (20441, 1), (482387, 1), (2068579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (37, 1), (173, 1), (20441, 1), (482387, 1), (2068579, 1)] : List FactorBlock).map factorBlockValue).prod) = 12011728285836368416157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_37
      · exact prime_oneHundredSixtyThreeFE_173
      · exact prime_oneHundredSixtyThreeFE_20441
      · exact prime_oneHundredSixtyThreeFE_482387
      · exact prime_oneHundredSixtyThreeFE_2068579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12011728285836368416157) ^ 6005864142918184208078 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 522249055905929061572 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 324641305022604551788 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 69431955409458776972 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 587629190638245116 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 24900605293750388 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 12011728285836368416157) ^ 5806753469814964 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_29603488293950764112441 : Nat.Prime 29603488293950764112441 := by
  apply lucas_primality 29603488293950764112441 (3 : ZMod 29603488293950764112441)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (43, 1), (1013, 1), (16990454495024429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (43, 1), (1013, 1), (16990454495024429, 1)] : List FactorBlock).map factorBlockValue).prod) = 29603488293950764112441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_43
      · exact prime_oneHundredSixtyThreeFE_1013
      · exact prime_oneHundredSixtyThreeFE_16990454495024429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29603488293950764112441) ^ 14801744146975382056220 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29603488293950764112441) ^ 5920697658790152822488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29603488293950764112441) ^ 688453216138389863080 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29603488293950764112441) ^ 29223581731442017880 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29603488293950764112441) ^ 1742360 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_37150846418948745673133 : Nat.Prime 37150846418948745673133 := by
  apply lucas_primality 37150846418948745673133 (2 : ZMod 37150846418948745673133)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (317, 1), (769, 1), (2213, 1), (1012727922251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (317, 1), (769, 1), (2213, 1), (1012727922251, 1)] : List FactorBlock).map factorBlockValue).prod) = 37150846418948745673133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_317
      · exact prime_oneHundredSixtyThreeFE_769
      · exact prime_oneHundredSixtyThreeFE_2213
      · exact prime_oneHundredSixtyThreeFE_1012727922251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37150846418948745673133) ^ 18575423209474372836566 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37150846418948745673133) ^ 2185343906996985039596 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37150846418948745673133) ^ 117195099113402983196 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37150846418948745673133) ^ 48310593522690176428 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37150846418948745673133) ^ 16787549217780725564 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37150846418948745673133) ^ 36683936132 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_47293507171658881092353 : Nat.Prime 47293507171658881092353 := by
  apply lucas_primality 47293507171658881092353 (3 : ZMod 47293507171658881092353)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (7258946483, 1), (25450010249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (7258946483, 1), (25450010249, 1)] : List FactorBlock).map factorBlockValue).prod) = 47293507171658881092353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7258946483
      · exact prime_oneHundredSixtyThreeFE_25450010249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47293507171658881092353) ^ 23646753585829440546176 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47293507171658881092353) ^ 6515202623744 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 47293507171658881092353) ^ 1858290299648 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_76386605022145892285671 : Nat.Prime 76386605022145892285671 := by
  apply lucas_primality 76386605022145892285671 (3 : ZMod 76386605022145892285671)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2546220167404863076189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2546220167404863076189, 1)] : List FactorBlock).map factorBlockValue).prod) = 76386605022145892285671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_2546220167404863076189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 76386605022145892285671) ^ 38193302511072946142835 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76386605022145892285671) ^ 25462201674048630761890 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76386605022145892285671) ^ 15277321004429178457134 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 76386605022145892285671) ^ 30 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_123103709990877906359141 : Nat.Prime 123103709990877906359141 := by
  apply lucas_primality 123103709990877906359141 (10 : ZMod 123103709990877906359141)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (6155185499543895317957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (6155185499543895317957, 1)] : List FactorBlock).map factorBlockValue).prod) = 123103709990877906359141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_6155185499543895317957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 123103709990877906359141) ^ 61551854995438953179570 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 123103709990877906359141) ^ 24620741998175581271828 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (10 : ZMod 123103709990877906359141) ^ 20 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_134875449055540508011187 : Nat.Prime 134875449055540508011187 := by
  apply lucas_primality 134875449055540508011187 (2 : ZMod 134875449055540508011187)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (311, 1), (2719428071, 1), (11391132479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (311, 1), (2719428071, 1), (11391132479, 1)] : List FactorBlock).map factorBlockValue).prod) = 134875449055540508011187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_311
      · exact prime_oneHundredSixtyThreeFE_2719428071
      · exact prime_oneHundredSixtyThreeFE_11391132479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 134875449055540508011187) ^ 67437724527770254005593 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 134875449055540508011187) ^ 19267921293648644001598 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 134875449055540508011187) ^ 433683115934213852126 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 134875449055540508011187) ^ 49596990813566 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 134875449055540508011187) ^ 11840389821134 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_152781446182087203765161 : Nat.Prime 152781446182087203765161 := by
  apply lucas_primality 152781446182087203765161 (3 : ZMod 152781446182087203765161)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (3776317, 1), (1011444789871237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (3776317, 1), (1011444789871237, 1)] : List FactorBlock).map factorBlockValue).prod) = 152781446182087203765161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_3776317
      · exact prime_oneHundredSixtyThreeFE_1011444789871237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 152781446182087203765161) ^ 76390723091043601882580 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 152781446182087203765161) ^ 30556289236417440753032 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 152781446182087203765161) ^ 40457791594849480 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 152781446182087203765161) ^ 151052680 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_296654606245849512067031 : Nat.Prime 296654606245849512067031 := by
  apply lucas_primality 296654606245849512067031 (11 : ZMod 296654606245849512067031)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (29, 1), (991, 1), (810437, 1), (97975351717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (29, 1), (991, 1), (810437, 1), (97975351717, 1)] : List FactorBlock).map factorBlockValue).prod) = 296654606245849512067031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_29
      · exact prime_oneHundredSixtyThreeFE_991
      · exact prime_oneHundredSixtyThreeFE_810437
      · exact prime_oneHundredSixtyThreeFE_97975351717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 296654606245849512067031) ^ 148327303122924756033515 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 59330921249169902413406 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 22819585095834577851310 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 10229469180891362485070 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 299348744950403140330 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 366042772289332190 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 296654606245849512067031) ^ 3027849362590 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_309906055186545651694271 : Nat.Prime 309906055186545651694271 := by
  apply lucas_primality 309906055186545651694271 (11 : ZMod 309906055186545651694271)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (6793, 1), (20359, 1), (775379227789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (6793, 1), (20359, 1), (775379227789, 1)] : List FactorBlock).map factorBlockValue).prod) = 309906055186545651694271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_6793
      · exact prime_oneHundredSixtyThreeFE_20359
      · exact prime_oneHundredSixtyThreeFE_775379227789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 309906055186545651694271) ^ 154953027593272825847135 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 309906055186545651694271) ^ 61981211037309130338854 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 309906055186545651694271) ^ 18229767952149744217310 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 309906055186545651694271) ^ 45621383068827565390 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 309906055186545651694271) ^ 15222066662731256530 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 309906055186545651694271) ^ 399683205430 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_455139019831368457101311 : Nat.Prime 455139019831368457101311 := by
  apply lucas_primality 455139019831368457101311 (7 : ZMod 455139019831368457101311)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (101, 1), (1509307, 1), (1033111669397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (101, 1), (1509307, 1), (1033111669397, 1)] : List FactorBlock).map factorBlockValue).prod) = 455139019831368457101311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_101
      · exact prime_oneHundredSixtyThreeFE_1509307
      · exact prime_oneHundredSixtyThreeFE_1033111669397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 455139019831368457101311) ^ 227569509915684228550655 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 455139019831368457101311) ^ 91027803966273691420262 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 455139019831368457101311) ^ 26772883519492262182430 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 455139019831368457101311) ^ 4506326929023450070310 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 455139019831368457101311) ^ 301554965180290330 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 455139019831368457101311) ^ 440551620230 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_927437722806335601766963 : Nat.Prime 927437722806335601766963 := by
  apply lucas_primality 927437722806335601766963 (2 : ZMod 927437722806335601766963)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (103, 1), (263, 1), (14737, 1), (24631, 1), (2245698067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (103, 1), (263, 1), (14737, 1), (24631, 1), (2245698067, 1)] : List FactorBlock).map factorBlockValue).prod) = 927437722806335601766963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_103
      · exact prime_oneHundredSixtyThreeFE_263
      · exact prime_oneHundredSixtyThreeFE_14737
      · exact prime_oneHundredSixtyThreeFE_24631
      · exact prime_oneHundredSixtyThreeFE_2245698067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 927437722806335601766963) ^ 463718861403167800883481 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 309145907602111867255654 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 132491103258047943109566 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 9004249735983840793854 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 3526379174168576432574 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 62932599769718097426 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 37653271195092996702 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 927437722806335601766963) ^ 412984156879686 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_1222589847413845960541237 : Nat.Prime 1222589847413845960541237 := by
  apply lucas_primality 1222589847413845960541237 (2 : ZMod 1222589847413845960541237)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (87037, 1), (184826091416331403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (87037, 1), (184826091416331403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1222589847413845960541237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_87037
      · exact prime_oneHundredSixtyThreeFE_184826091416331403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1222589847413845960541237) ^ 611294923706922980270618 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222589847413845960541237) ^ 64346834074412945291644 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222589847413845960541237) ^ 14046782947641186628 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1222589847413845960541237) ^ 6614812 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_3641112158650947656810489 : Nat.Prime 3641112158650947656810489 := by
  apply lucas_primality 3641112158650947656810489 (3 : ZMod 3641112158650947656810489)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (455139019831368457101311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (455139019831368457101311, 1)] : List FactorBlock).map factorBlockValue).prod) = 3641112158650947656810489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_455139019831368457101311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3641112158650947656810489) ^ 1820556079325473828405244 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3641112158650947656810489) ^ 8 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4534981458765003428351107 : Nat.Prime 4534981458765003428351107 := by
  apply lucas_primality 4534981458765003428351107 (2 : ZMod 4534981458765003428351107)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (211, 1), (511733407669262404463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (211, 1), (511733407669262404463, 1)] : List FactorBlock).map factorBlockValue).prod) = 4534981458765003428351107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_211
      · exact prime_oneHundredSixtyThreeFE_511733407669262404463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4534981458765003428351107) ^ 2267490729382501714175553 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4534981458765003428351107) ^ 1511660486255001142783702 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4534981458765003428351107) ^ 647854494109286204050158 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4534981458765003428351107) ^ 21492803122109020987446 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4534981458765003428351107) ^ 8862 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_6474148428030640854812603 : Nat.Prime 6474148428030640854812603 := by
  apply lucas_primality 6474148428030640854812603 (5 : ZMod 6474148428030640854812603)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (7079, 1), (65325494198440466317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (7079, 1), (65325494198440466317, 1)] : List FactorBlock).map factorBlockValue).prod) = 6474148428030640854812603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_7079
      · exact prime_oneHundredSixtyThreeFE_65325494198440466317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6474148428030640854812603) ^ 3237074214015320427406301 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6474148428030640854812603) ^ 924878346861520122116086 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6474148428030640854812603) ^ 914556918778166528438 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6474148428030640854812603) ^ 99106 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_7116566420796929564767973 : Nat.Prime 7116566420796929564767973 := by
  apply lucas_primality 7116566420796929564767973 (2 : ZMod 7116566420796929564767973)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (95219, 1), (18684733143587229347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (95219, 1), (18684733143587229347, 1)] : List FactorBlock).map factorBlockValue).prod) = 7116566420796929564767973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_95219
      · exact prime_oneHundredSixtyThreeFE_18684733143587229347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7116566420796929564767973) ^ 3558283210398464782383986 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7116566420796929564767973) ^ 74738932574348917388 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7116566420796929564767973) ^ 380876 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10309180019727173577507727 : Nat.Prime 10309180019727173577507727 := by
  apply lucas_primality 10309180019727173577507727 (3 : ZMod 10309180019727173577507727)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1471, 1), (20023, 1), (2536315156044419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1471, 1), (20023, 1), (2536315156044419, 1)] : List FactorBlock).map factorBlockValue).prod) = 10309180019727173577507727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_23
      · exact prime_oneHundredSixtyThreeFE_1471
      · exact prime_oneHundredSixtyThreeFE_20023
      · exact prime_oneHundredSixtyThreeFE_2536315156044419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10309180019727173577507727) ^ 5154590009863586788753863 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10309180019727173577507727) ^ 3436393339909057859169242 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10309180019727173577507727) ^ 448225218249007546848162 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10309180019727173577507727) ^ 7008280094987881425906 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10309180019727173577507727) ^ 514866904046704968162 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10309180019727173577507727) ^ 4064628954 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_11776430097088734764382299 : Nat.Prime 11776430097088734764382299 := by
  apply lucas_primality 11776430097088734764382299 (2 : ZMod 11776430097088734764382299)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (309906055186545651694271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (309906055186545651694271, 1)] : List FactorBlock).map factorBlockValue).prod) = 11776430097088734764382299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_309906055186545651694271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11776430097088734764382299) ^ 5888215048544367382191149 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776430097088734764382299) ^ 619812110373091303388542 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 11776430097088734764382299) ^ 38 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_12071504767524433455546977 : Nat.Prime 12071504767524433455546977 := by
  apply lucas_primality 12071504767524433455546977 (3 : ZMod 12071504767524433455546977)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (283, 1), (421, 1), (13164301, 1), (240516622601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (283, 1), (421, 1), (13164301, 1), (240516622601, 1)] : List FactorBlock).map factorBlockValue).prod) = 12071504767524433455546977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_283
      · exact prime_oneHundredSixtyThreeFE_421
      · exact prime_oneHundredSixtyThreeFE_13164301
      · exact prime_oneHundredSixtyThreeFE_240516622601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12071504767524433455546977) ^ 6035752383762216727773488 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12071504767524433455546977) ^ 42655493878178210090272 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12071504767524433455546977) ^ 28673407998870388255456 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12071504767524433455546977) ^ 916987902929630176 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12071504767524433455546977) ^ 50189898049376 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_94790704431264169052804693 : Nat.Prime 94790704431264169052804693 := by
  apply lucas_primality 94790704431264169052804693 (2 : ZMod 94790704431264169052804693)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1063, 1), (1597, 1), (21143, 1), (453559, 1), (1455684239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1063, 1), (1597, 1), (21143, 1), (453559, 1), (1455684239, 1)] : List FactorBlock).map factorBlockValue).prod) = 94790704431264169052804693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_1063
      · exact prime_oneHundredSixtyThreeFE_1597
      · exact prime_oneHundredSixtyThreeFE_21143
      · exact prime_oneHundredSixtyThreeFE_453559
      · exact prime_oneHundredSixtyThreeFE_1455684239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94790704431264169052804693) ^ 47395352215632084526402346 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94790704431264169052804693) ^ 89172816962619161855884 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94790704431264169052804693) ^ 59355481797911189137636 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94790704431264169052804693) ^ 4483313835844684720844 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94790704431264169052804693) ^ 208993106588699968588 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94790704431264169052804693) ^ 65117627773714028 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_97772451602617988678007073 : Nat.Prime 97772451602617988678007073 := by
  apply lucas_primality 97772451602617988678007073 (5 : ZMod 97772451602617988678007073)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (19, 1), (53802349, 1), (332100232058599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (19, 1), (53802349, 1), (332100232058599, 1)] : List FactorBlock).map factorBlockValue).prod) = 97772451602617988678007073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_19
      · exact prime_oneHundredSixtyThreeFE_53802349
      · exact prime_oneHundredSixtyThreeFE_332100232058599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 97772451602617988678007073) ^ 48886225801308994339003536 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 97772451602617988678007073) ^ 32590817200872662892669024 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 97772451602617988678007073) ^ 5145918505400946772526688 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 97772451602617988678007073) ^ 1817252469824653728 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 97772451602617988678007073) ^ 294406453728 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_321718701350183732361188549 : Nat.Prime 321718701350183732361188549 := by
  apply lucas_primality 321718701350183732361188549 (2 : ZMod 321718701350183732361188549)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (661, 1), (1103, 1), (321621611504589173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (661, 1), (1103, 1), (321621611504589173, 1)] : List FactorBlock).map factorBlockValue).prod) = 321718701350183732361188549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_661
      · exact prime_oneHundredSixtyThreeFE_1103
      · exact prime_oneHundredSixtyThreeFE_321621611504589173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 321718701350183732361188549) ^ 160859350675091866180594274 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321718701350183732361188549) ^ 45959814478597676051598364 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321718701350183732361188549) ^ 486715130635678868927668 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321718701350183732361188549) ^ 291676066500619884280316 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 321718701350183732361188549) ^ 1000301876 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_373468027342558247450294459 : Nat.Prime 373468027342558247450294459 := by
  apply lucas_primality 373468027342558247450294459 (2 : ZMod 373468027342558247450294459)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13766867, 1), (450401153, 1), (30115412879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13766867, 1), (450401153, 1), (30115412879, 1)] : List FactorBlock).map factorBlockValue).prod) = 373468027342558247450294459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_13766867
      · exact prime_oneHundredSixtyThreeFE_450401153
      · exact prime_oneHundredSixtyThreeFE_30115412879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 373468027342558247450294459) ^ 186734013671279123725147229 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373468027342558247450294459) ^ 27128033367545298974 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373468027342558247450294459) ^ 829189767510560186 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373468027342558247450294459) ^ 12401225539995302 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_407419666191881724491230319 : Nat.Prime 407419666191881724491230319 := by
  apply lucas_primality 407419666191881724491230319 (11 : ZMod 407419666191881724491230319)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (16691, 1), (189797, 1), (5845849187225947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (16691, 1), (189797, 1), (5845849187225947, 1)] : List FactorBlock).map factorBlockValue).prod) = 407419666191881724491230319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_11
      · exact prime_oneHundredSixtyThreeFE_16691
      · exact prime_oneHundredSixtyThreeFE_189797
      · exact prime_oneHundredSixtyThreeFE_5845849187225947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 407419666191881724491230319) ^ 203709833095940862245615159 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 407419666191881724491230319) ^ 37038151471989247681020938 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 407419666191881724491230319) ^ 24409542040134307380698 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 407419666191881724491230319) ^ 2146607513247742190294 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (11 : ZMod 407419666191881724491230319) ^ 69693837994 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_4700231758750245260593949777 : Nat.Prime 4700231758750245260593949777 := by
  apply lucas_primality 4700231758750245260593949777 (3 : ZMod 4700231758750245260593949777)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (1103155829, 1), (6494991232212649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (1103155829, 1), (6494991232212649, 1)] : List FactorBlock).map factorBlockValue).prod) = 4700231758750245260593949777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_41
      · exact prime_oneHundredSixtyThreeFE_1103155829
      · exact prime_oneHundredSixtyThreeFE_6494991232212649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4700231758750245260593949777) ^ 2350115879375122630296974888 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700231758750245260593949777) ^ 114639798993908420990096336 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700231758750245260593949777) ^ 4260714248331497744 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 4700231758750245260593949777) ^ 723670223824 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8029562587865002320181330867 : Nat.Prime 8029562587865002320181330867 := by
  apply lucas_primality 8029562587865002320181330867 (3 : ZMod 8029562587865002320181330867)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1553, 1), (123103709990877906359141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1553, 1), (123103709990877906359141, 1)] : List FactorBlock).map factorBlockValue).prod) = 8029562587865002320181330867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_1553
      · exact prime_oneHundredSixtyThreeFE_123103709990877906359141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8029562587865002320181330867) ^ 4014781293932501160090665433 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8029562587865002320181330867) ^ 2676520862621667440060443622 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8029562587865002320181330867) ^ 1147080369695000331454475838 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8029562587865002320181330867) ^ 5170355819616872067083922 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8029562587865002320181330867) ^ 65226 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_8378674004728698073232693081 : Nat.Prime 8378674004728698073232693081 := by
  apply lucas_primality 8378674004728698073232693081 (15 : ZMod 8378674004728698073232693081)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 2), (7433, 1), (11887, 1), (112601, 1), (429675488113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 2), (7433, 1), (11887, 1), (112601, 1), (429675488113, 1)] : List FactorBlock).map factorBlockValue).prod) = 8378674004728698073232693081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_7
      · exact prime_oneHundredSixtyThreeFE_7433
      · exact prime_oneHundredSixtyThreeFE_11887
      · exact prime_oneHundredSixtyThreeFE_112601
      · exact prime_oneHundredSixtyThreeFE_429675488113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 8378674004728698073232693081) ^ 4189337002364349036616346540 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 1675734800945739614646538616 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 1196953429246956867604670440 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 1127226423345714795268760 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 704860267916942716684840 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 74410298351956892685080 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (15 : ZMod 8378674004728698073232693081) ^ 19500004623315160 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_10706083450486669760241774491 : Nat.Prime 10706083450486669760241774491 := by
  apply lucas_primality 10706083450486669760241774491 (2 : ZMod 10706083450486669760241774491)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (137, 1), (5419, 1), (81883, 1), (31329941, 1), (33066533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (137, 1), (5419, 1), (81883, 1), (31329941, 1), (33066533, 1)] : List FactorBlock).map factorBlockValue).prod) = 10706083450486669760241774491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_5
      · exact prime_oneHundredSixtyThreeFE_17
      · exact prime_oneHundredSixtyThreeFE_137
      · exact prime_oneHundredSixtyThreeFE_5419
      · exact prime_oneHundredSixtyThreeFE_81883
      · exact prime_oneHundredSixtyThreeFE_31329941
      · exact prime_oneHundredSixtyThreeFE_33066533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10706083450486669760241774491) ^ 5353041725243334880120887245 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 2141216690097333952048354898 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 629769614734509985896574970 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 78146594529099779271837770 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 1975656661835517578933710 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 130748549155339566946030 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 341720511075544947890 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706083450486669760241774491) ^ 323773993798704864530 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_19270950210876005568435194089 : Nat.Prime 19270950210876005568435194089 := by
  apply lucas_primality 19270950210876005568435194089 (7 : ZMod 19270950210876005568435194089)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (40429, 1), (477047, 1), (3202538555710673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (40429, 1), (477047, 1), (3202538555710673, 1)] : List FactorBlock).map factorBlockValue).prod) = 19270950210876005568435194089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_13
      · exact prime_oneHundredSixtyThreeFE_40429
      · exact prime_oneHundredSixtyThreeFE_477047
      · exact prime_oneHundredSixtyThreeFE_3202538555710673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 19270950210876005568435194089) ^ 9635475105438002784217597044 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 19270950210876005568435194089) ^ 6423650070292001856145064696 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 19270950210876005568435194089) ^ 1482380785452000428341168776 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 19270950210876005568435194089) ^ 476661560040466139860872 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 19270950210876005568435194089) ^ 40396334555873961199704 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (7 : ZMod 19270950210876005568435194089) ^ 6017398346856 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyThreeFE_64236500702920018561450646953 : Nat.Prime 64236500702920018561450646953 := by
  apply lucas_primality 64236500702920018561450646953 (5 : ZMod 64236500702920018561450646953)
  · rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (296251, 1), (334616262288805831199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (296251, 1), (334616262288805831199, 1)] : List FactorBlock).map factorBlockValue).prod) = 64236500702920018561450646953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyThreeFE_2
      · exact prime_oneHundredSixtyThreeFE_3
      · exact prime_oneHundredSixtyThreeFE_296251
      · exact prime_oneHundredSixtyThreeFE_334616262288805831199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 64236500702920018561450646953) ^ 32118250351460009280725323476 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 64236500702920018561450646953) ^ 21412166900973339520483548984 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 64236500702920018561450646953) ^ 216831337963146178616952 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide
    · change (5 : ZMod 64236500702920018561450646953) ^ 191970648 ≠ 1
      rw [← oneHundredSixtyThreeFEFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940800 : Nat.totient 192709502108760055684351940800 = 76610447001111036186436608000 := by
  rw [← show ((([(2, 6), (5, 2), (163, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_163, prime_oneHundredSixtyThreeFE_171401, prime_oneHundredSixtyThreeFE_714027719, prime_oneHundredSixtyThreeFE_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940801 : Nat.totient 192709502108760055684351940801 = 188227882665870099340808857680 := by
  rw [← show ((([(43, 1), (96397823, 1), (162054799, 1), (286883487091, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_43, prime_oneHundredSixtyThreeFE_96397823, prime_oneHundredSixtyThreeFE_162054799, prime_oneHundredSixtyThreeFE_286883487091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940802 : Nat.totient 192709502108760055684351940802 = 59295231381048649299688040064 := by
  rw [← show ((([(2, 1), (3, 3), (13, 1), (1601216359, 1), (171441516148592489, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_1601216359, prime_oneHundredSixtyThreeFE_171441516148592489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940803 : Nat.totient 192709502108760055684351940803 = 181315831494843491558134865920 := by
  rw [← show ((([(17, 1), (3137, 1), (501133510967, 1), (7210846391621, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_3137, prime_oneHundredSixtyThreeFE_501133510967, prime_oneHundredSixtyThreeFE_7210846391621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940804 : Nat.totient 192709502108760055684351940804 = 96354751053125656671106079304 := by
  rw [← show ((([(2, 2), (76815192407, 1), (627185508719753143, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_76815192407, prime_oneHundredSixtyThreeFE_627185508719753143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940805 : Nat.totient 192709502108760055684351940805 = 85266036955599266183235851520 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (37, 2), (191, 1), (7019028646705856035579, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_37, prime_oneHundredSixtyThreeFE_191, prime_oneHundredSixtyThreeFE_7019028646705856035579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940806 : Nat.totient 192709502108760055684351940806 = 96354741322826265261581430840 := by
  rw [← show ((([(2, 1), (9901271, 1), (9731553762580584638293, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_9901271, prime_oneHundredSixtyThreeFE_9731553762580584638293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940807 : Nat.totient 192709502108760055684351940807 = 190996411409300326808095004160 := by
  rw [← show ((([(127, 1), (977, 1), (354262255981, 1), (4384095043693, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_127, prime_oneHundredSixtyThreeFE_977, prime_oneHundredSixtyThreeFE_354262255981, prime_oneHundredSixtyThreeFE_4384095043693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940808 : Nat.totient 192709502108760055684351940808 = 64236500702920018561450646928 := by
  rw [← show ((([(2, 3), (3, 1), (8029562587865002320181330867, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_8029562587865002320181330867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940809 : Nat.totient 192709502108760055684351940809 = 192541049930319776264130048000 := by
  rw [← show ((([(1201, 1), (27077, 1), (217937, 1), (27191214674521141, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_1201, prime_oneHundredSixtyThreeFE_27077, prime_oneHundredSixtyThreeFE_217937, prime_oneHundredSixtyThreeFE_27191214674521141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940810 : Nat.totient 192709502108760055684351940810 = 69116234878324004312699412480 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (73, 1), (2393862198593, 1), (10025093624939, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_73, prime_oneHundredSixtyThreeFE_2393862198593, prime_oneHundredSixtyThreeFE_10025093624939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940811 : Nat.totient 192709502108760055684351940811 = 122473058634358822100791784880 := by
  rw [← show ((([(3, 2), (31, 1), (67, 1), (10309180019727173577507727, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_31, prime_oneHundredSixtyThreeFE_67, prime_oneHundredSixtyThreeFE_10309180019727173577507727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940812 : Nat.totient 192709502108760055684351940812 = 75519889647046639777511294976 := by
  rw [← show ((([(2, 2), (7, 1), (19, 1), (29, 1), (4649, 1), (8599, 1), (312453938988510829, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_19, prime_oneHundredSixtyThreeFE_29, prime_oneHundredSixtyThreeFE_4649, prime_oneHundredSixtyThreeFE_8599, prime_oneHundredSixtyThreeFE_312453938988510829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940813 : Nat.totient 192709502108760055684351940813 = 192678524837562771526660778560 := by
  rw [← show ((([(6221, 1), (11750453837, 1), (2636260286571269, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_6221, prime_oneHundredSixtyThreeFE_11750453837, prime_oneHundredSixtyThreeFE_2636260286571269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940814 : Nat.totient 192709502108760055684351940814 = 64229218478602716666137008320 := by
  rw [← show ((([(2, 1), (3, 1), (8821, 1), (3641112158650947656810489, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_8821, prime_oneHundredSixtyThreeFE_3641112158650947656810489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940815 : Nat.totient 192709502108760055684351940815 = 142308555402014948024609314176 := by
  rw [← show ((([(5, 1), (13, 1), (103340194213, 1), (28689336162782627, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_103340194213, prime_oneHundredSixtyThreeFE_28689336162782627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940816 : Nat.totient 192709502108760055684351940816 = 94004635089790605771844577280 := by
  rw [← show ((([(2, 4), (41, 2), (1103155829, 1), (6494991232212649, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_41, prime_oneHundredSixtyThreeFE_1103155829, prime_oneHundredSixtyThreeFE_6494991232212649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940817 : Nat.totient 192709502108760055684351940817 = 122359341125163995730729105408 := by
  rw [← show ((([(3, 1), (23, 1), (239, 1), (8929, 1), (5161293727, 1), (253568171789, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_23, prime_oneHundredSixtyThreeFE_239, prime_oneHundredSixtyThreeFE_8929, prime_oneHundredSixtyThreeFE_5161293727, prime_oneHundredSixtyThreeFE_253568171789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940818 : Nat.totient 192709502108760055684351940818 = 96335898804456122409377891040 := by
  rw [← show ((([(2, 1), (5113, 1), (13383911, 1), (1408037757789001063, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5113, prime_oneHundredSixtyThreeFE_13383911, prime_oneHundredSixtyThreeFE_1408037757789001063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940819 : Nat.totient 192709502108760055684351940819 = 165179573225527085171782913160 := by
  rw [← show ((([(7, 1), (15652436347, 1), (1758827077291164911, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_15652436347, prime_oneHundredSixtyThreeFE_1758827077291164911]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940820 : Nat.totient 192709502108760055684351940820 = 48003818267460771135500451840 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (17, 1), (137, 1), (5419, 1), (81883, 1), (31329941, 1), (33066533, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_137, prime_oneHundredSixtyThreeFE_5419, prime_oneHundredSixtyThreeFE_81883, prime_oneHundredSixtyThreeFE_31329941, prime_oneHundredSixtyThreeFE_33066533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940821 : Nat.totient 192709502108760055684351940821 = 174557959078931804116585353600 := by
  rw [← show ((([(11, 1), (367, 1), (1129, 1), (448871, 1), (94195225462005487, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_367, prime_oneHundredSixtyThreeFE_1129, prime_oneHundredSixtyThreeFE_448871, prime_oneHundredSixtyThreeFE_94195225462005487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940822 : Nat.totient 192709502108760055684351940822 = 96354749868608366441811513000 := by
  rw [← show ((([(2, 1), (81259111, 1), (1185771661400283198301, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_81259111, prime_oneHundredSixtyThreeFE_1185771661400283198301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940823 : Nat.totient 192709502108760055684351940823 = 127847639349667840619689574400 := by
  rw [← show ((([(3, 1), (433, 1), (601, 1), (1109, 1), (222580933818977582753, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_433, prime_oneHundredSixtyThreeFE_601, prime_oneHundredSixtyThreeFE_1109, prime_oneHundredSixtyThreeFE_222580933818977582753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940824 : Nat.totient 192709502108760055684351940824 = 96309746498420080859195372800 := by
  rw [← show ((([(2, 3), (2141, 1), (63354172991, 1), (177591121131113, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_2141, prime_oneHundredSixtyThreeFE_63354172991, prime_oneHundredSixtyThreeFE_177591121131113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940825 : Nat.totient 192709502108760055684351940825 = 154167601686081640062821006160 := by
  rw [← show ((([(5, 2), (166415597207, 1), (46320057817430119, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_166415597207, prime_oneHundredSixtyThreeFE_46320057817430119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940826 : Nat.totient 192709502108760055684351940826 = 54638758719059935649181151680 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (131, 1), (68749, 1), (509467116610384709087, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_131, prime_oneHundredSixtyThreeFE_68749, prime_oneHundredSixtyThreeFE_509467116610384709087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940827 : Nat.totient 192709502108760055684351940827 = 189527095632704658719635077120 := by
  rw [← show ((([(61, 1), (13723, 1), (20117, 1), (11443556418146214977, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_61, prime_oneHundredSixtyThreeFE_13723, prime_oneHundredSixtyThreeFE_20117, prime_oneHundredSixtyThreeFE_11443556418146214977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940828 : Nat.totient 192709502108760055684351940828 = 88653131012699439297536991744 := by
  rw [← show ((([(2, 2), (13, 1), (307, 1), (12071504767524433455546977, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_307, prime_oneHundredSixtyThreeFE_12071504767524433455546977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940829 : Nat.totient 192709502108760055684351940829 = 128462592832994270273924358000 := by
  rw [← show ((([(3, 3), (12343, 1), (122990042251, 1), (4701632561939, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_12343, prime_oneHundredSixtyThreeFE_122990042251, prime_oneHundredSixtyThreeFE_4701632561939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940830 : Nat.totient 192709502108760055684351940830 = 77011657984287917377499189760 := by
  rw [← show ((([(2, 1), (5, 1), (1069, 1), (2230097, 1), (8083541470050947231, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_1069, prime_oneHundredSixtyThreeFE_2230097, prime_oneHundredSixtyThreeFE_8083541470050947231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940831 : Nat.totient 192709502108760055684351940831 = 182566896700735100612862336600 := by
  rw [← show ((([(19, 1), (5388682799, 1), (1882204938102400651, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_19, prime_oneHundredSixtyThreeFE_5388682799, prime_oneHundredSixtyThreeFE_1882204938102400651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940832 : Nat.totient 192709502108760055684351940832 = 58322796603113217278301120000 := by
  rw [← show ((([(2, 5), (3, 1), (11, 1), (811, 1), (28927, 1), (7778842196081819851, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_811, prime_oneHundredSixtyThreeFE_28927, prime_oneHundredSixtyThreeFE_7778842196081819851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940833 : Nat.totient 192709502108760055684351940833 = 165174731272629977150696472000 := by
  rw [← show ((([(7, 1), (34483, 1), (5956663, 1), (6867551, 1), (19516193861, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_34483, prime_oneHundredSixtyThreeFE_5956663, prime_oneHundredSixtyThreeFE_6867551, prime_oneHundredSixtyThreeFE_19516193861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940834 : Nat.totient 192709502108760055684351940834 = 92559369106057482935227924800 := by
  rw [← show ((([(2, 1), (47, 1), (71, 1), (223, 1), (828221, 1), (156338458647727427, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_47, prime_oneHundredSixtyThreeFE_71, prime_oneHundredSixtyThreeFE_223, prime_oneHundredSixtyThreeFE_828221, prime_oneHundredSixtyThreeFE_156338458647727427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940835 : Nat.totient 192709502108760055684351940835 = 102651907731506503443294565248 := by
  rw [← show ((([(3, 1), (5, 1), (829, 1), (40823, 1), (379622917713639092567, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_829, prime_oneHundredSixtyThreeFE_40823, prime_oneHundredSixtyThreeFE_379622917713639092567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940836 : Nat.totient 192709502108760055684351940836 = 96331198194185850372647197640 := by
  rw [← show ((([(2, 2), (4091, 1), (11776430097088734764382299, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_4091, prime_oneHundredSixtyThreeFE_11776430097088734764382299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940837 : Nat.totient 192709502108760055684351940837 = 181373647803518997433096161472 := by
  rw [← show ((([(17, 1), (146266727, 1), (77501242406423572643, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_146266727, prime_oneHundredSixtyThreeFE_77501242406423572643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940838 : Nat.totient 192709502108760055684351940838 = 64236500702920018561450646940 := by
  rw [← show ((([(2, 1), (3, 2), (10706083450486669760241774491, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_10706083450486669760241774491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940839 : Nat.totient 192709502108760055684351940839 = 192361397011856238815017789560 := by
  rw [← show ((([(563, 1), (33083, 1), (10346413936805375815591, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_563, prime_oneHundredSixtyThreeFE_33083, prime_oneHundredSixtyThreeFE_10346413936805375815591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940840 : Nat.totient 192709502108760055684351940840 = 63184761467654693245540761600 := by
  rw [← show ((([(2, 3), (5, 1), (7, 2), (23, 1), (7433, 1), (11887, 1), (112601, 1), (429675488113, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_23, prime_oneHundredSixtyThreeFE_7433, prime_oneHundredSixtyThreeFE_11887, prime_oneHundredSixtyThreeFE_112601, prime_oneHundredSixtyThreeFE_429675488113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940841 : Nat.totient 192709502108760055684351940841 = 114495995265399957216209529600 := by
  rw [← show ((([(3, 1), (13, 1), (29, 1), (22271, 1), (7650693548963475662341, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_29, prime_oneHundredSixtyThreeFE_22271, prime_oneHundredSixtyThreeFE_7650693548963475662341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940842 : Nat.totient 192709502108760055684351940842 = 90386347144014874118301696000 := by
  rw [← show ((([(2, 1), (31, 1), (37, 1), (419, 1), (733, 1), (349951009, 1), (781599851401, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_31, prime_oneHundredSixtyThreeFE_37, prime_oneHundredSixtyThreeFE_419, prime_oneHundredSixtyThreeFE_733, prime_oneHundredSixtyThreeFE_349951009, prime_oneHundredSixtyThreeFE_781599851401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940843 : Nat.totient 192709502108760055684351940843 = 174811929273966087839704348800 := by
  rw [← show ((([(11, 1), (643, 1), (1667, 1), (153421, 1), (106531750254190013, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_643, prime_oneHundredSixtyThreeFE_1667, prime_oneHundredSixtyThreeFE_153421, prime_oneHundredSixtyThreeFE_106531750254190013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940844 : Nat.totient 192709502108760055684351940844 = 62742628593549785571649468944 := by
  rw [← show ((([(2, 2), (3, 1), (43, 1), (373468027342558247450294459, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_43, prime_oneHundredSixtyThreeFE_373468027342558247450294459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940845 : Nat.totient 192709502108760055684351940845 = 152633853170653182124211251200 := by
  rw [← show ((([(5, 1), (103, 1), (4129, 1), (355616587, 1), (254840828248301, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_103, prime_oneHundredSixtyThreeFE_4129, prime_oneHundredSixtyThreeFE_355616587, prime_oneHundredSixtyThreeFE_254840828248301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940846 : Nat.totient 192709502108760055684351940846 = 96301887192670207933522008288 := by
  rw [← show ((([(2, 1), (1823, 1), (10925389, 1), (4837818333499727309, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_1823, prime_oneHundredSixtyThreeFE_10925389, prime_oneHundredSixtyThreeFE_4837818333499727309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940847 : Nat.totient 192709502108760055684351940847 = 107920178937230973948940032000 := by
  rw [← show ((([(3, 2), (7, 1), (53, 1), (887, 1), (79126090529, 1), (822324788251, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_53, prime_oneHundredSixtyThreeFE_887, prime_oneHundredSixtyThreeFE_79126090529, prime_oneHundredSixtyThreeFE_822324788251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940848 : Nat.totient 192709502108760055684351940848 = 96078175762348956155616000000 := by
  rw [← show ((([(2, 4), (677, 1), (1051, 1), (2251, 1), (23379331, 1), (321650467769, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_677, prime_oneHundredSixtyThreeFE_1051, prime_oneHundredSixtyThreeFE_2251, prime_oneHundredSixtyThreeFE_23379331, prime_oneHundredSixtyThreeFE_321650467769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940849 : Nat.totient 192709502108760055684351940849 = 192709472505271761733581318720 := by
  rw [← show ((([(6509689, 1), (29603488293950764112441, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_6509689, prime_oneHundredSixtyThreeFE_29603488293950764112441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940850 : Nat.totient 192709502108760055684351940850 = 48684449377632110544198144000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (19, 1), (862921, 1), (78358701620389862561, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_19, prime_oneHundredSixtyThreeFE_862921, prime_oneHundredSixtyThreeFE_78358701620389862561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940851 : Nat.totient 192709502108760055684351940851 = 192387783407409871951990751704 := by
  rw [← show ((([(599, 1), (321718701350183732361188549, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_599, prime_oneHundredSixtyThreeFE_321718701350183732361188549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940852 : Nat.totient 192709502108760055684351940852 = 96354481303481916761159233656 := by
  rw [← show ((([(2, 2), (357199, 1), (134875449055540508011187, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_357199, prime_oneHundredSixtyThreeFE_134875449055540508011187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940853 : Nat.totient 192709502108760055684351940853 = 128468939779622538853899878400 := by
  rw [← show ((([(3, 1), (33587, 1), (570217, 1), (11423669, 1), (293605974401, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_33587, prime_oneHundredSixtyThreeFE_570217, prime_oneHundredSixtyThreeFE_11423669, prime_oneHundredSixtyThreeFE_293605974401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940854 : Nat.totient 192709502108760055684351940854 = 64123703271062080451299952640 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (13, 1), (17, 1), (59, 1), (6972298243, 1), (13764554738563, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_59, prime_oneHundredSixtyThreeFE_6972298243, prime_oneHundredSixtyThreeFE_13764554738563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940855 : Nat.totient 192709502108760055684351940855 = 152310150858701070951664039200 := by
  rw [← show ((([(5, 1), (83, 1), (15472187, 1), (30012579737124748651, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_83, prime_oneHundredSixtyThreeFE_15472187, prime_oneHundredSixtyThreeFE_30012579737124748651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940856 : Nat.totient 192709502108760055684351940856 = 64236283871582055415080060000 := by
  rw [← show ((([(2, 3), (3, 5), (296251, 1), (334616262288805831199, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_296251, prime_oneHundredSixtyThreeFE_334616262288805831199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940857 : Nat.totient 192709502108760055684351940857 = 188009270350009810423757991040 := by
  rw [← show ((([(41, 1), (4700231758750245260593949777, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_41, prime_oneHundredSixtyThreeFE_4700231758750245260593949777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940858 : Nat.totient 192709502108760055684351940858 = 96350216072921262838747598076 := by
  rw [← show ((([(2, 1), (21247, 1), (4534981458765003428351107, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_21247, prime_oneHundredSixtyThreeFE_4534981458765003428351107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940859 : Nat.totient 192709502108760055684351940859 = 128473001405840037122901293904 := by
  rw [← show ((([(3, 1), (64236500702920018561450646953, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_64236500702920018561450646953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940860 : Nat.totient 192709502108760055684351940860 = 76489406905336552427110207488 := by
  rw [← show ((([(2, 2), (5, 1), (167, 1), (577, 1), (3796339, 1), (26340005596089943, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_167, prime_oneHundredSixtyThreeFE_577, prime_oneHundredSixtyThreeFE_3796339, prime_oneHundredSixtyThreeFE_26340005596089943]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940861 : Nat.totient 192709502108760055684351940861 = 165179350331001534036966035760 := by
  rw [← show ((([(7, 1), (741031, 1), (37150846418948745673133, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_741031, prime_oneHundredSixtyThreeFE_37150846418948745673133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940862 : Nat.totient 192709502108760055684351940862 = 63801300743474742980133840000 := by
  rw [← show ((([(2, 1), (3, 1), (227, 1), (421, 1), (205031, 1), (1639171506015686701, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_227, prime_oneHundredSixtyThreeFE_421, prime_oneHundredSixtyThreeFE_205031, prime_oneHundredSixtyThreeFE_1639171506015686701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940863 : Nat.totient 192709502108760055684351940863 = 184330828104031357611119247760 := by
  rw [← show ((([(23, 1), (8378674004728698073232693081, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_23, prime_oneHundredSixtyThreeFE_8378674004728698073232693081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940864 : Nat.totient 192709502108760055684351940864 = 95940297911444248626521800704 := by
  rw [← show ((([(2, 8), (263, 1), (1997, 1), (5055563, 1), (283504413317233, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_263, prime_oneHundredSixtyThreeFE_1997, prime_oneHundredSixtyThreeFE_5055563, prime_oneHundredSixtyThreeFE_283504413317233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940865 : Nat.totient 192709502108760055684351940865 = 93432027298549608088227830400 := by
  rw [← show ((([(3, 2), (5, 1), (11, 1), (32411, 1), (12011728285836368416157, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_32411, prime_oneHundredSixtyThreeFE_12011728285836368416157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940866 : Nat.totient 192709502108760055684351940866 = 96350919288386928197163684768 := by
  rw [← show ((([(2, 1), (25219, 1), (8723123, 1), (437999158137460009, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_25219, prime_oneHundredSixtyThreeFE_8723123, prime_oneHundredSixtyThreeFE_437999158137460009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940867 : Nat.totient 192709502108760055684351940867 = 177800295457190488246163012448 := by
  rw [← show ((([(13, 1), (2083, 1), (7116566420796929564767973, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_2083, prime_oneHundredSixtyThreeFE_7116566420796929564767973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940868 : Nat.totient 192709502108760055684351940868 = 54550222912078219807162490880 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (179, 1), (271, 1), (47293507171658881092353, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_179, prime_oneHundredSixtyThreeFE_271, prime_oneHundredSixtyThreeFE_47293507171658881092353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940869 : Nat.totient 192709502108760055684351940869 = 180860664054852034552751352336 := by
  rw [← show ((([(19, 1), (107, 1), (94790704431264169052804693, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_19, prime_oneHundredSixtyThreeFE_107, prime_oneHundredSixtyThreeFE_94790704431264169052804693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940870 : Nat.totient 192709502108760055684351940870 = 74283433263928579106208780288 := by
  rw [← show ((([(2, 1), (5, 1), (29, 1), (523, 1), (1382996977, 1), (918717971202793, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_29, prime_oneHundredSixtyThreeFE_523, prime_oneHundredSixtyThreeFE_1382996977, prime_oneHundredSixtyThreeFE_918717971202793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940871 : Nat.totient 192709502108760055684351940871 = 119845714992353681534032134144 := by
  rw [← show ((([(3, 1), (17, 1), (113, 1), (12146541829, 1), (2752972414571273, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_113, prime_oneHundredSixtyThreeFE_12146541829, prime_oneHundredSixtyThreeFE_2752972414571273]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940872 : Nat.totient 192709502108760055684351940872 = 96354751053917309138270782464 := by
  rw [← show ((([(2, 3), (208236502417, 1), (115679467739794577, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_208236502417, prime_oneHundredSixtyThreeFE_115679467739794577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940873 : Nat.totient 192709502108760055684351940873 = 186493049566815427091397181440 := by
  rw [← show ((([(31, 1), (15515809, 1), (37520129, 1), (10678314013303, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_31, prime_oneHundredSixtyThreeFE_15515809, prime_oneHundredSixtyThreeFE_37520129, prime_oneHundredSixtyThreeFE_10678314013303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940874 : Nat.totient 192709502108760055684351940874 = 64236497331347373751339076064 := by
  rw [← show ((([(2, 1), (3, 2), (19414223, 1), (1024190423, 1), (538430806117, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_19414223, prime_oneHundredSixtyThreeFE_1024190423, prime_oneHundredSixtyThreeFE_538430806117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940875 : Nat.totient 192709502108760055684351940875 = 129999253263077478665548800000 := by
  rw [← show ((([(5, 3), (7, 1), (79, 1), (379, 1), (1021, 1), (7204486517949553601, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_79, prime_oneHundredSixtyThreeFE_379, prime_oneHundredSixtyThreeFE_1021, prime_oneHundredSixtyThreeFE_7204486517949553601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940876 : Nat.totient 192709502108760055684351940876 = 86611012183554117470238720000 := by
  rw [← show ((([(2, 2), (11, 1), (89, 1), (550617305201, 1), (89373875307361, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_89, prime_oneHundredSixtyThreeFE_550617305201, prime_oneHundredSixtyThreeFE_89373875307361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940877 : Nat.totient 192709502108760055684351940877 = 128412869925483997755751372608 := by
  rw [← show ((([(3, 1), (3307, 1), (6389, 1), (108799, 1), (27944084630306567, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_3307, prime_oneHundredSixtyThreeFE_6389, prime_oneHundredSixtyThreeFE_108799, prime_oneHundredSixtyThreeFE_27944084630306567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940878 : Nat.totient 192709502108760055684351940878 = 94578838874220157992425167200 := by
  rw [← show ((([(2, 1), (67, 2), (281, 1), (76386605022145892285671, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_67, prime_oneHundredSixtyThreeFE_281, prime_oneHundredSixtyThreeFE_76386605022145892285671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940879 : Nat.totient 192709502108760055684351940879 = 184542897453418064466658022400 := by
  rw [← show ((([(37, 1), (97, 1), (181, 1), (296654606245849512067031, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_37, prime_oneHundredSixtyThreeFE_97, prime_oneHundredSixtyThreeFE_181, prime_oneHundredSixtyThreeFE_296654606245849512067031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940880 : Nat.totient 192709502108760055684351940880 = 47434912379029157515025154048 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (13, 1), (40429, 1), (477047, 1), (3202538555710673, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_40429, prime_oneHundredSixtyThreeFE_477047, prime_oneHundredSixtyThreeFE_3202538555710673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940881 : Nat.totient 192709502108760055684351940881 = 188566637800984154551258713840 := by
  rw [← show ((([(47, 1), (4421, 1), (927437722806335601766963, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_47, prime_oneHundredSixtyThreeFE_4421, prime_oneHundredSixtyThreeFE_927437722806335601766963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940882 : Nat.totient 192709502108760055684351940882 = 82589680108522937957802640704 := by
  rw [← show ((([(2, 1), (7, 1), (783703, 1), (73381813, 1), (239350945294117, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_783703, prime_oneHundredSixtyThreeFE_73381813, prime_oneHundredSixtyThreeFE_239350945294117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940883 : Nat.totient 192709502108760055684351940883 = 126713097276992913326697165312 := by
  rw [← show ((([(3, 3), (73, 1), (97772451602617988678007073, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_73, prime_oneHundredSixtyThreeFE_97772451602617988678007073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940884 : Nat.totient 192709502108760055684351940884 = 96354748092232906341743235360 := by
  rw [← show ((([(2, 2), (49798079, 1), (93800671, 1), (10313940058469, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_49798079, prime_oneHundredSixtyThreeFE_93800671, prime_oneHundredSixtyThreeFE_10313940058469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940885 : Nat.totient 192709502108760055684351940885 = 154167600418100973859080239104 := by
  rw [← show ((([(5, 1), (121496369, 1), (317226767671978832033, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_121496369, prime_oneHundredSixtyThreeFE_317226767671978832033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940886 : Nat.totient 192709502108760055684351940886 = 61438768023258159247726898688 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (12697, 1), (28951177, 1), (3798889829124463, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_23, prime_oneHundredSixtyThreeFE_12697, prime_oneHundredSixtyThreeFE_28951177, prime_oneHundredSixtyThreeFE_3798889829124463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940887 : Nat.totient 192709502108760055684351940887 = 171116259800590324286316733560 := by
  rw [← show ((([(11, 1), (43, 1), (407419666191881724491230319, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_43, prime_oneHundredSixtyThreeFE_407419666191881724491230319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940888 : Nat.totient 192709502108760055684351940888 = 84505410253245032792610232320 := by
  rw [← show ((([(2, 3), (17, 1), (19, 1), (61, 1), (1222589847413845960541237, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_17, prime_oneHundredSixtyThreeFE_19, prime_oneHundredSixtyThreeFE_61, prime_oneHundredSixtyThreeFE_1222589847413845960541237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940889 : Nat.totient 192709502108760055684351940889 = 109578599705479750560110592000 := by
  rw [← show ((([(3, 1), (7, 2), (233, 1), (1601, 1), (8874181, 1), (396013744414319, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_233, prime_oneHundredSixtyThreeFE_1601, prime_oneHundredSixtyThreeFE_8874181, prime_oneHundredSixtyThreeFE_396013744414319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940890 : Nat.totient 192709502108760055684351940890 = 77083800843504022273740776352 := by
  rw [← show ((([(2, 1), (5, 1), (19270950210876005568435194089, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_19270950210876005568435194089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940891 : Nat.totient 192709502108760055684351940891 = 191334982366964659942384848000 := by
  rw [← show ((([(151, 1), (2029, 1), (49603, 1), (2082413, 1), (6089327402311, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_151, prime_oneHundredSixtyThreeFE_2029, prime_oneHundredSixtyThreeFE_49603, prime_oneHundredSixtyThreeFE_2082413, prime_oneHundredSixtyThreeFE_6089327402311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940892 : Nat.totient 192709502108760055684351940892 = 64236245235372206240518856736 := by
  rw [← show ((([(2, 2), (3, 2), (251483, 1), (1747679783, 1), (12179518900123, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_251483, prime_oneHundredSixtyThreeFE_1747679783, prime_oneHundredSixtyThreeFE_12179518900123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940893 : Nat.totient 192709502108760055684351940893 = 177705358290491390052215126400 := by
  rw [← show ((([(13, 1), (1033, 1), (21851, 1), (656731939826732175467, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_13, prime_oneHundredSixtyThreeFE_1033, prime_oneHundredSixtyThreeFE_21851, prime_oneHundredSixtyThreeFE_656731939826732175467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940894 : Nat.totient 192709502108760055684351940894 = 96347040823522224987518585472 := by
  rw [← show ((([(2, 1), (12497, 1), (306552390803, 1), (25151428502917, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_12497, prime_oneHundredSixtyThreeFE_306552390803, prime_oneHundredSixtyThreeFE_25151428502917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940895 : Nat.totient 192709502108760055684351940895 = 102778400739529147409549627904 := by
  rw [← show ((([(3, 1), (5, 1), (266857849, 1), (48142860285829568057, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_266857849, prime_oneHundredSixtyThreeFE_48142860285829568057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940896 : Nat.totient 192709502108760055684351940896 = 82493353252568767111506432000 := by
  rw [← show ((([(2, 5), (7, 1), (1237, 1), (2851, 1), (114277, 1), (2134663200379421, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_7, prime_oneHundredSixtyThreeFE_1237, prime_oneHundredSixtyThreeFE_2851, prime_oneHundredSixtyThreeFE_114277, prime_oneHundredSixtyThreeFE_2134663200379421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940897 : Nat.totient 192709502108760055684351940897 = 190800633340613388161710080000 := by
  rw [← show ((([(101, 1), (251219, 1), (2905921, 1), (6756241, 1), (386847983, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_101, prime_oneHundredSixtyThreeFE_251219, prime_oneHundredSixtyThreeFE_2905921, prime_oneHundredSixtyThreeFE_6756241, prime_oneHundredSixtyThreeFE_386847983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940898 : Nat.totient 192709502108760055684351940898 = 56972506166669639522350897600 := by
  rw [← show ((([(2, 1), (3, 1), (11, 2), (41, 1), (6474148428030640854812603, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_11, prime_oneHundredSixtyThreeFE_41, prime_oneHundredSixtyThreeFE_6474148428030640854812603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940899 : Nat.totient 192709502108760055684351940899 = 186064344682864623763167433536 := by
  rw [← show ((([(29, 1), (85320647, 1), (77884491958079702473, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_29, prime_oneHundredSixtyThreeFE_85320647, prime_oneHundredSixtyThreeFE_77884491958079702473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940900 : Nat.totient 192709502108760055684351940900 = 74935505548417059628281239040 := by
  rw [← show ((([(2, 2), (5, 2), (53, 1), (109, 1), (2061599, 1), (161806724685557183, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_2, prime_oneHundredSixtyThreeFE_5, prime_oneHundredSixtyThreeFE_53, prime_oneHundredSixtyThreeFE_109, prime_oneHundredSixtyThreeFE_2061599, prime_oneHundredSixtyThreeFE_161806724685557183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyThreeFE_192709502108760055684351940901 : Nat.totient 192709502108760055684351940901 = 127749734039614036300276185600 := by
  rw [← show ((([(3, 2), (269, 1), (521, 1), (152781446182087203765161, 1)] : List FactorBlock).map factorBlockValue).prod) = 192709502108760055684351940901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyThreeFE_3, prime_oneHundredSixtyThreeFE_269, prime_oneHundredSixtyThreeFE_521, prime_oneHundredSixtyThreeFE_152781446182087203765161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyThreeFE : certifiedKill 1 192709502108760055684351940799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940800, phi_oneHundredSixtyThreeFE_192709502108760055684351940801, phi_oneHundredSixtyThreeFE_192709502108760055684351940802,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940803, phi_oneHundredSixtyThreeFE_192709502108760055684351940804, phi_oneHundredSixtyThreeFE_192709502108760055684351940805,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940806, phi_oneHundredSixtyThreeFE_192709502108760055684351940807, phi_oneHundredSixtyThreeFE_192709502108760055684351940808,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940809, phi_oneHundredSixtyThreeFE_192709502108760055684351940810, phi_oneHundredSixtyThreeFE_192709502108760055684351940811,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940812, phi_oneHundredSixtyThreeFE_192709502108760055684351940813, phi_oneHundredSixtyThreeFE_192709502108760055684351940814,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940815, phi_oneHundredSixtyThreeFE_192709502108760055684351940816, phi_oneHundredSixtyThreeFE_192709502108760055684351940817,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940818, phi_oneHundredSixtyThreeFE_192709502108760055684351940819, phi_oneHundredSixtyThreeFE_192709502108760055684351940820,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940821, phi_oneHundredSixtyThreeFE_192709502108760055684351940822, phi_oneHundredSixtyThreeFE_192709502108760055684351940823,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940824, phi_oneHundredSixtyThreeFE_192709502108760055684351940825, phi_oneHundredSixtyThreeFE_192709502108760055684351940826,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940827, phi_oneHundredSixtyThreeFE_192709502108760055684351940828, phi_oneHundredSixtyThreeFE_192709502108760055684351940829,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940830, phi_oneHundredSixtyThreeFE_192709502108760055684351940831, phi_oneHundredSixtyThreeFE_192709502108760055684351940832,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940833, phi_oneHundredSixtyThreeFE_192709502108760055684351940834, phi_oneHundredSixtyThreeFE_192709502108760055684351940835,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940836, phi_oneHundredSixtyThreeFE_192709502108760055684351940837, phi_oneHundredSixtyThreeFE_192709502108760055684351940838,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940839, phi_oneHundredSixtyThreeFE_192709502108760055684351940840, phi_oneHundredSixtyThreeFE_192709502108760055684351940841,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940842, phi_oneHundredSixtyThreeFE_192709502108760055684351940843, phi_oneHundredSixtyThreeFE_192709502108760055684351940844,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940845, phi_oneHundredSixtyThreeFE_192709502108760055684351940846, phi_oneHundredSixtyThreeFE_192709502108760055684351940847,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940848, phi_oneHundredSixtyThreeFE_192709502108760055684351940849, phi_oneHundredSixtyThreeFE_192709502108760055684351940850,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940851, phi_oneHundredSixtyThreeFE_192709502108760055684351940852, phi_oneHundredSixtyThreeFE_192709502108760055684351940853,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940854, phi_oneHundredSixtyThreeFE_192709502108760055684351940855, phi_oneHundredSixtyThreeFE_192709502108760055684351940856,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940857, phi_oneHundredSixtyThreeFE_192709502108760055684351940858, phi_oneHundredSixtyThreeFE_192709502108760055684351940859,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940860, phi_oneHundredSixtyThreeFE_192709502108760055684351940861, phi_oneHundredSixtyThreeFE_192709502108760055684351940862,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940863, phi_oneHundredSixtyThreeFE_192709502108760055684351940864, phi_oneHundredSixtyThreeFE_192709502108760055684351940865,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940866, phi_oneHundredSixtyThreeFE_192709502108760055684351940867, phi_oneHundredSixtyThreeFE_192709502108760055684351940868,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940869, phi_oneHundredSixtyThreeFE_192709502108760055684351940870, phi_oneHundredSixtyThreeFE_192709502108760055684351940871,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940872, phi_oneHundredSixtyThreeFE_192709502108760055684351940873, phi_oneHundredSixtyThreeFE_192709502108760055684351940874,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940875, phi_oneHundredSixtyThreeFE_192709502108760055684351940876, phi_oneHundredSixtyThreeFE_192709502108760055684351940877,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940878, phi_oneHundredSixtyThreeFE_192709502108760055684351940879, phi_oneHundredSixtyThreeFE_192709502108760055684351940880,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940881, phi_oneHundredSixtyThreeFE_192709502108760055684351940882, phi_oneHundredSixtyThreeFE_192709502108760055684351940883,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940884, phi_oneHundredSixtyThreeFE_192709502108760055684351940885, phi_oneHundredSixtyThreeFE_192709502108760055684351940886,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940887, phi_oneHundredSixtyThreeFE_192709502108760055684351940888, phi_oneHundredSixtyThreeFE_192709502108760055684351940889,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940890, phi_oneHundredSixtyThreeFE_192709502108760055684351940891, phi_oneHundredSixtyThreeFE_192709502108760055684351940892,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940893, phi_oneHundredSixtyThreeFE_192709502108760055684351940894, phi_oneHundredSixtyThreeFE_192709502108760055684351940895,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940896, phi_oneHundredSixtyThreeFE_192709502108760055684351940897, phi_oneHundredSixtyThreeFE_192709502108760055684351940898,
    phi_oneHundredSixtyThreeFE_192709502108760055684351940899, phi_oneHundredSixtyThreeFE_192709502108760055684351940900, phi_oneHundredSixtyThreeFE_192709502108760055684351940901
    ]

end TotientTailPeriodKiller
end Erdos249257

