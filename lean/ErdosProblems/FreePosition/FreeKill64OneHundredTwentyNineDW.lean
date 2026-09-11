import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentyNineDWFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentyNineDWFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentyNineDWFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentyNineDWFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentyNineDWFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentyNineDWFastPow a n * oneHundredTwentyNineDWFastPow a n * a else oneHundredTwentyNineDWFastPow a n * oneHundredTwentyNineDWFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentyNineDW_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentyNineDW_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentyNineDW_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentyNineDW_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentyNineDW_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentyNineDW_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentyNineDW_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentyNineDW_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentyNineDW_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentyNineDW_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentyNineDW_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentyNineDW_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentyNineDW_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentyNineDW_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentyNineDW_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentyNineDW_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentyNineDW_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentyNineDW_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentyNineDW_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentyNineDW_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentyNineDW_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentyNineDW_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentyNineDW_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentyNineDW_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentyNineDW_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentyNineDW_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentyNineDW_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentyNineDW_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentyNineDW_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentyNineDW_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentyNineDW_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentyNineDW_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentyNineDW_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentyNineDW_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentyNineDW_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentyNineDW_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentyNineDW_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentyNineDW_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentyNineDW_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentyNineDW_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentyNineDW_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentyNineDW_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentyNineDW_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentyNineDW_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentyNineDW_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentyNineDW_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentyNineDW_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredTwentyNineDW_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentyNineDW_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentyNineDW_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentyNineDW_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredTwentyNineDW_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentyNineDW_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredTwentyNineDW_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredTwentyNineDW_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentyNineDW_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwentyNineDW_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentyNineDW_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentyNineDW_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwentyNineDW_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredTwentyNineDW_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredTwentyNineDW_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentyNineDW_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentyNineDW_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredTwentyNineDW_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentyNineDW_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentyNineDW_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentyNineDW_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentyNineDW_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentyNineDW_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredTwentyNineDW_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentyNineDW_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredTwentyNineDW_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredTwentyNineDW_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredTwentyNineDW_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredTwentyNineDW_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentyNineDW_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTwentyNineDW_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredTwentyNineDW_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredTwentyNineDW_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredTwentyNineDW_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredTwentyNineDW_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredTwentyNineDW_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentyNineDW_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwentyNineDW_661 : Nat.Prime 661 := by norm_num

private theorem prime_oneHundredTwentyNineDW_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentyNineDW_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredTwentyNineDW_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwentyNineDW_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredTwentyNineDW_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredTwentyNineDW_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredTwentyNineDW_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentyNineDW_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredTwentyNineDW_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredTwentyNineDW_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwentyNineDW_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredTwentyNineDW_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredTwentyNineDW_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredTwentyNineDW_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredTwentyNineDW_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1093 : Nat.Prime 1093 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1163 : Nat.Prime 1163 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1297 : Nat.Prime 1297 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1327 : Nat.Prime 1327 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1663 : Nat.Prime 1663 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1933 : Nat.Prime 1933 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2003 : Nat.Prime 2003 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2089 : Nat.Prime 2089 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2503 : Nat.Prime 2503 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2689 : Nat.Prime 2689 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2749 : Nat.Prime 2749 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2837 : Nat.Prime 2837 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2953 : Nat.Prime 2953 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2999 : Nat.Prime 2999 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3167 : Nat.Prime 3167 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3343 : Nat.Prime 3343 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3389 : Nat.Prime 3389 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3413 : Nat.Prime 3413 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3517 : Nat.Prime 3517 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3557 : Nat.Prime 3557 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3571 : Nat.Prime 3571 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3613 : Nat.Prime 3613 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3697 : Nat.Prime 3697 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3709 : Nat.Prime 3709 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3923 : Nat.Prime 3923 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4073 : Nat.Prime 4073 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4253 : Nat.Prime 4253 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4391 : Nat.Prime 4391 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4447 : Nat.Prime 4447 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4513 : Nat.Prime 4513 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4789 : Nat.Prime 4789 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4943 : Nat.Prime 4943 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5023 : Nat.Prime 5023 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5179 : Nat.Prime 5179 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5507 : Nat.Prime 5507 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6079 : Nat.Prime 6079 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6257 : Nat.Prime 6257 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6673 : Nat.Prime 6673 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6823 : Nat.Prime 6823 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7001 : Nat.Prime 7001 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7103 : Nat.Prime 7103 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7523 : Nat.Prime 7523 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7589 : Nat.Prime 7589 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7669 : Nat.Prime 7669 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7901 : Nat.Prime 7901 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7993 : Nat.Prime 7993 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8117 : Nat.Prime 8117 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8123 : Nat.Prime 8123 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8329 : Nat.Prime 8329 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8389 : Nat.Prime 8389 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8969 : Nat.Prime 8969 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8971 : Nat.Prime 8971 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9601 : Nat.Prime 9601 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9623 : Nat.Prime 9623 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9839 : Nat.Prime 9839 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10009 : Nat.Prime 10009 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10069 : Nat.Prime 10069 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10657 : Nat.Prime 10657 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10903 : Nat.Prime 10903 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10949 : Nat.Prime 10949 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11093 : Nat.Prime 11093 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11411 : Nat.Prime 11411 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11867 : Nat.Prime 11867 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11903 : Nat.Prime 11903 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11959 : Nat.Prime 11959 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12409 : Nat.Prime 12409 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12503 : Nat.Prime 12503 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12511 : Nat.Prime 12511 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12569 : Nat.Prime 12569 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12659 : Nat.Prime 12659 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13829 : Nat.Prime 13829 := by norm_num

private theorem prime_oneHundredTwentyNineDW_14731 : Nat.Prime 14731 := by norm_num

private theorem prime_oneHundredTwentyNineDW_15241 : Nat.Prime 15241 := by norm_num

private theorem prime_oneHundredTwentyNineDW_15791 : Nat.Prime 15791 := by norm_num

private theorem prime_oneHundredTwentyNineDW_15937 : Nat.Prime 15937 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16069 : Nat.Prime 16069 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16103 : Nat.Prime 16103 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16633 : Nat.Prime 16633 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16931 : Nat.Prime 16931 := by norm_num

private theorem prime_oneHundredTwentyNineDW_17191 : Nat.Prime 17191 := by norm_num

private theorem prime_oneHundredTwentyNineDW_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentyNineDW_17783 : Nat.Prime 17783 := by norm_num

private theorem prime_oneHundredTwentyNineDW_17977 : Nat.Prime 17977 := by norm_num

private theorem prime_oneHundredTwentyNineDW_18127 : Nat.Prime 18127 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19087 : Nat.Prime 19087 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19753 : Nat.Prime 19753 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19819 : Nat.Prime 19819 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19861 : Nat.Prime 19861 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20129 : Nat.Prime 20129 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20149 : Nat.Prime 20149 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20297 : Nat.Prime 20297 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20809 : Nat.Prime 20809 := by norm_num

private theorem prime_oneHundredTwentyNineDW_22031 : Nat.Prime 22031 := by norm_num

private theorem prime_oneHundredTwentyNineDW_22541 : Nat.Prime 22541 := by norm_num

private theorem prime_oneHundredTwentyNineDW_23537 : Nat.Prime 23537 := by norm_num

private theorem prime_oneHundredTwentyNineDW_24517 : Nat.Prime 24517 := by norm_num

private theorem prime_oneHundredTwentyNineDW_24677 : Nat.Prime 24677 := by norm_num

private theorem prime_oneHundredTwentyNineDW_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredTwentyNineDW_25127 : Nat.Prime 25127 := by norm_num

private theorem prime_oneHundredTwentyNineDW_26699 : Nat.Prime 26699 := by norm_num

private theorem prime_oneHundredTwentyNineDW_28711 : Nat.Prime 28711 := by norm_num

private theorem prime_oneHundredTwentyNineDW_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredTwentyNineDW_32119 : Nat.Prime 32119 := by norm_num

private theorem prime_oneHundredTwentyNineDW_32191 : Nat.Prime 32191 := by norm_num

private theorem prime_oneHundredTwentyNineDW_33829 : Nat.Prime 33829 := by norm_num

private theorem prime_oneHundredTwentyNineDW_35363 : Nat.Prime 35363 := by norm_num

private theorem prime_oneHundredTwentyNineDW_36677 : Nat.Prime 36677 := by norm_num

private theorem prime_oneHundredTwentyNineDW_40939 : Nat.Prime 40939 := by norm_num

private theorem prime_oneHundredTwentyNineDW_42433 : Nat.Prime 42433 := by norm_num

private theorem prime_oneHundredTwentyNineDW_43427 : Nat.Prime 43427 := by norm_num

private theorem prime_oneHundredTwentyNineDW_43777 : Nat.Prime 43777 := by norm_num

private theorem prime_oneHundredTwentyNineDW_44017 : Nat.Prime 44017 := by norm_num

private theorem prime_oneHundredTwentyNineDW_44111 : Nat.Prime 44111 := by norm_num

private theorem prime_oneHundredTwentyNineDW_44893 : Nat.Prime 44893 := by norm_num

private theorem prime_oneHundredTwentyNineDW_45989 : Nat.Prime 45989 := by norm_num

private theorem prime_oneHundredTwentyNineDW_47237 : Nat.Prime 47237 := by norm_num

private theorem prime_oneHundredTwentyNineDW_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredTwentyNineDW_48491 : Nat.Prime 48491 := by norm_num

private theorem prime_oneHundredTwentyNineDW_48593 : Nat.Prime 48593 := by norm_num

private theorem prime_oneHundredTwentyNineDW_49739 : Nat.Prime 49739 := by norm_num

private theorem prime_oneHundredTwentyNineDW_50909 : Nat.Prime 50909 := by norm_num

private theorem prime_oneHundredTwentyNineDW_51991 : Nat.Prime 51991 := by norm_num

private theorem prime_oneHundredTwentyNineDW_52903 : Nat.Prime 52903 := by norm_num

private theorem prime_oneHundredTwentyNineDW_54559 : Nat.Prime 54559 := by norm_num

private theorem prime_oneHundredTwentyNineDW_56113 : Nat.Prime 56113 := by norm_num

private theorem prime_oneHundredTwentyNineDW_57427 : Nat.Prime 57427 := by norm_num

private theorem prime_oneHundredTwentyNineDW_59393 : Nat.Prime 59393 := by norm_num

private theorem prime_oneHundredTwentyNineDW_59497 : Nat.Prime 59497 := by norm_num

private theorem prime_oneHundredTwentyNineDW_59879 : Nat.Prime 59879 := by norm_num

private theorem prime_oneHundredTwentyNineDW_62563 : Nat.Prime 62563 := by norm_num

private theorem prime_oneHundredTwentyNineDW_64997 : Nat.Prime 64997 := by norm_num

private theorem prime_oneHundredTwentyNineDW_65447 : Nat.Prime 65447 := by norm_num

private theorem prime_oneHundredTwentyNineDW_67079 : Nat.Prime 67079 := by norm_num

private theorem prime_oneHundredTwentyNineDW_67807 : Nat.Prime 67807 := by norm_num

private theorem prime_oneHundredTwentyNineDW_69313 : Nat.Prime 69313 := by norm_num

private theorem prime_oneHundredTwentyNineDW_69697 : Nat.Prime 69697 := by norm_num

private theorem prime_oneHundredTwentyNineDW_71479 : Nat.Prime 71479 := by norm_num

private theorem prime_oneHundredTwentyNineDW_73847 : Nat.Prime 73847 := by norm_num

private theorem prime_oneHundredTwentyNineDW_82883 : Nat.Prime 82883 := by norm_num

private theorem prime_oneHundredTwentyNineDW_87541 : Nat.Prime 87541 := by norm_num

private theorem prime_oneHundredTwentyNineDW_87973 : Nat.Prime 87973 := by norm_num

private theorem prime_oneHundredTwentyNineDW_94781 : Nat.Prime 94781 := by norm_num

private theorem prime_oneHundredTwentyNineDW_95443 : Nat.Prime 95443 := by norm_num

private theorem prime_oneHundredTwentyNineDW_101203 : Nat.Prime 101203 := by norm_num

private theorem prime_oneHundredTwentyNineDW_103067 : Nat.Prime 103067 := by norm_num

private theorem prime_oneHundredTwentyNineDW_113189 : Nat.Prime 113189 := by norm_num

private theorem prime_oneHundredTwentyNineDW_115153 : Nat.Prime 115153 := by norm_num

private theorem prime_oneHundredTwentyNineDW_115769 : Nat.Prime 115769 := by norm_num

private theorem prime_oneHundredTwentyNineDW_125669 : Nat.Prime 125669 := by norm_num

private theorem prime_oneHundredTwentyNineDW_126443 : Nat.Prime 126443 := by norm_num

private theorem prime_oneHundredTwentyNineDW_127301 : Nat.Prime 127301 := by norm_num

private theorem prime_oneHundredTwentyNineDW_127931 : Nat.Prime 127931 := by norm_num

private theorem prime_oneHundredTwentyNineDW_130147 : Nat.Prime 130147 := by norm_num

private theorem prime_oneHundredTwentyNineDW_133673 : Nat.Prime 133673 := by norm_num

private theorem prime_oneHundredTwentyNineDW_139591 : Nat.Prime 139591 := by norm_num

private theorem prime_oneHundredTwentyNineDW_147151 : Nat.Prime 147151 := by norm_num

private theorem prime_oneHundredTwentyNineDW_150077 : Nat.Prime 150077 := by norm_num

private theorem prime_oneHundredTwentyNineDW_151901 : Nat.Prime 151901 := by norm_num

private theorem prime_oneHundredTwentyNineDW_152837 : Nat.Prime 152837 := by norm_num

private theorem prime_oneHundredTwentyNineDW_154213 : Nat.Prime 154213 := by norm_num

private theorem prime_oneHundredTwentyNineDW_156319 : Nat.Prime 156319 := by norm_num

private theorem prime_oneHundredTwentyNineDW_156491 : Nat.Prime 156491 := by norm_num

private theorem prime_oneHundredTwentyNineDW_169489 : Nat.Prime 169489 := by norm_num

private theorem prime_oneHundredTwentyNineDW_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentyNineDW_172553 : Nat.Prime 172553 := by norm_num

private theorem prime_oneHundredTwentyNineDW_179381 : Nat.Prime 179381 := by norm_num

private theorem prime_oneHundredTwentyNineDW_190667 : Nat.Prime 190667 := by norm_num

private theorem prime_oneHundredTwentyNineDW_191699 : Nat.Prime 191699 := by norm_num

private theorem prime_oneHundredTwentyNineDW_192547 : Nat.Prime 192547 := by norm_num

private theorem prime_oneHundredTwentyNineDW_207401 : Nat.Prime 207401 := by norm_num

private theorem prime_oneHundredTwentyNineDW_237233 : Nat.Prime 237233 := by norm_num

private theorem prime_oneHundredTwentyNineDW_241663 : Nat.Prime 241663 := by norm_num

private theorem prime_oneHundredTwentyNineDW_260417 : Nat.Prime 260417 := by norm_num

private theorem prime_oneHundredTwentyNineDW_270157 : Nat.Prime 270157 := by norm_num

private theorem prime_oneHundredTwentyNineDW_281683 : Nat.Prime 281683 := by norm_num

private theorem prime_oneHundredTwentyNineDW_301027 : Nat.Prime 301027 := by norm_num

private theorem prime_oneHundredTwentyNineDW_305741 : Nat.Prime 305741 := by norm_num

private theorem prime_oneHundredTwentyNineDW_314747 : Nat.Prime 314747 := by norm_num

private theorem prime_oneHundredTwentyNineDW_314983 : Nat.Prime 314983 := by norm_num

private theorem prime_oneHundredTwentyNineDW_321163 : Nat.Prime 321163 := by norm_num

private theorem prime_oneHundredTwentyNineDW_327619 : Nat.Prime 327619 := by norm_num

private theorem prime_oneHundredTwentyNineDW_330731 : Nat.Prime 330731 := by norm_num

private theorem prime_oneHundredTwentyNineDW_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredTwentyNineDW_360439 : Nat.Prime 360439 := by norm_num

private theorem prime_oneHundredTwentyNineDW_364739 : Nat.Prime 364739 := by norm_num

private theorem prime_oneHundredTwentyNineDW_378733 : Nat.Prime 378733 := by norm_num

private theorem prime_oneHundredTwentyNineDW_383767 : Nat.Prime 383767 := by norm_num

private theorem prime_oneHundredTwentyNineDW_390479 : Nat.Prime 390479 := by norm_num

private theorem prime_oneHundredTwentyNineDW_391049 : Nat.Prime 391049 := by norm_num

private theorem prime_oneHundredTwentyNineDW_399757 : Nat.Prime 399757 := by norm_num

private theorem prime_oneHundredTwentyNineDW_425959 : Nat.Prime 425959 := by norm_num

private theorem prime_oneHundredTwentyNineDW_455513 : Nat.Prime 455513 := by norm_num

private theorem prime_oneHundredTwentyNineDW_486041 : Nat.Prime 486041 := by norm_num

private theorem prime_oneHundredTwentyNineDW_489299 : Nat.Prime 489299 := by norm_num

private theorem prime_oneHundredTwentyNineDW_504767 : Nat.Prime 504767 := by norm_num

private theorem prime_oneHundredTwentyNineDW_505283 : Nat.Prime 505283 := by norm_num

private theorem prime_oneHundredTwentyNineDW_505781 : Nat.Prime 505781 := by norm_num

private theorem prime_oneHundredTwentyNineDW_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredTwentyNineDW_522811 : Nat.Prime 522811 := by norm_num

private theorem prime_oneHundredTwentyNineDW_553591 : Nat.Prime 553591 := by norm_num

private theorem prime_oneHundredTwentyNineDW_612971 : Nat.Prime 612971 := by norm_num

private theorem prime_oneHundredTwentyNineDW_616757 : Nat.Prime 616757 := by norm_num

private theorem prime_oneHundredTwentyNineDW_712571 : Nat.Prime 712571 := by norm_num

private theorem prime_oneHundredTwentyNineDW_755719 : Nat.Prime 755719 := by norm_num

private theorem prime_oneHundredTwentyNineDW_798647 : Nat.Prime 798647 := by norm_num

private theorem prime_oneHundredTwentyNineDW_924419 : Nat.Prime 924419 := by norm_num

private theorem prime_oneHundredTwentyNineDW_939767 : Nat.Prime 939767 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1019377 : Nat.Prime 1019377 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1072931 : Nat.Prime 1072931 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1076503 : Nat.Prime 1076503 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1127809 : Nat.Prime 1127809 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1167211 : Nat.Prime 1167211 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1211813 : Nat.Prime 1211813 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1262147 : Nat.Prime 1262147 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1325263 : Nat.Prime 1325263 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1405247 : Nat.Prime 1405247 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1417873 : Nat.Prime 1417873 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1425253 : Nat.Prime 1425253 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1470709 : Nat.Prime 1470709 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1470871 : Nat.Prime 1470871 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1536811 : Nat.Prime 1536811 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1543391 : Nat.Prime 1543391 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1641077 : Nat.Prime 1641077 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1918243 : Nat.Prime 1918243 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1974743 : Nat.Prime 1974743 := by norm_num

private theorem prime_oneHundredTwentyNineDW_1992433 : Nat.Prime 1992433 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2037643 : Nat.Prime 2037643 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2135533 : Nat.Prime 2135533 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2154811 : Nat.Prime 2154811 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2246869 : Nat.Prime 2246869 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2347907 : Nat.Prime 2347907 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2703577 : Nat.Prime 2703577 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2765671 : Nat.Prime 2765671 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2845061 : Nat.Prime 2845061 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2847601 : Nat.Prime 2847601 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2925437 : Nat.Prime 2925437 := by norm_num

private theorem prime_oneHundredTwentyNineDW_2943571 : Nat.Prime 2943571 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3007541 : Nat.Prime 3007541 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3056353 : Nat.Prime 3056353 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3215741 : Nat.Prime 3215741 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3221443 : Nat.Prime 3221443 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3308533 : Nat.Prime 3308533 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3539027 : Nat.Prime 3539027 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3628153 : Nat.Prime 3628153 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3725507 : Nat.Prime 3725507 := by norm_num

private theorem prime_oneHundredTwentyNineDW_3821203 : Nat.Prime 3821203 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4100521 : Nat.Prime 4100521 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4195861 : Nat.Prime 4195861 := by norm_num

private theorem prime_oneHundredTwentyNineDW_4359863 : Nat.Prime 4359863 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5580907 : Nat.Prime 5580907 := by norm_num

private theorem prime_oneHundredTwentyNineDW_5798267 : Nat.Prime 5798267 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6245791 : Nat.Prime 6245791 := by norm_num

private theorem prime_oneHundredTwentyNineDW_6349951 : Nat.Prime 6349951 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7182649 : Nat.Prime 7182649 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7431797 : Nat.Prime 7431797 := by norm_num

private theorem prime_oneHundredTwentyNineDW_7739887 : Nat.Prime 7739887 := by norm_num

private theorem prime_oneHundredTwentyNineDW_8046331 : Nat.Prime 8046331 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9346853 : Nat.Prime 9346853 := by norm_num

private theorem prime_oneHundredTwentyNineDW_9533897 : Nat.Prime 9533897 := by norm_num

private theorem prime_oneHundredTwentyNineDW_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11051801 : Nat.Prime 11051801 := by norm_num

private theorem prime_oneHundredTwentyNineDW_11674717 : Nat.Prime 11674717 := by norm_num

private theorem prime_oneHundredTwentyNineDW_12030229 : Nat.Prime 12030229 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13210577 : Nat.Prime 13210577 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13312043 : Nat.Prime 13312043 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13419463 : Nat.Prime 13419463 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13596767 : Nat.Prime 13596767 := by norm_num

private theorem prime_oneHundredTwentyNineDW_13642327 : Nat.Prime 13642327 := by norm_num

private theorem prime_oneHundredTwentyNineDW_14089463 : Nat.Prime 14089463 := by norm_num

private theorem prime_oneHundredTwentyNineDW_14287073 : Nat.Prime 14287073 := by norm_num

private theorem prime_oneHundredTwentyNineDW_14752421 : Nat.Prime 14752421 := by norm_num

private theorem prime_oneHundredTwentyNineDW_15901427 : Nat.Prime 15901427 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16614239 : Nat.Prime 16614239 := by norm_num

private theorem prime_oneHundredTwentyNineDW_16630729 : Nat.Prime 16630729 := by norm_num

private theorem prime_oneHundredTwentyNineDW_18661009 : Nat.Prime 18661009 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19147433 : Nat.Prime 19147433 := by norm_num

private theorem prime_oneHundredTwentyNineDW_19796017 : Nat.Prime 19796017 := by norm_num

private theorem prime_oneHundredTwentyNineDW_20628221 : Nat.Prime 20628221 := by norm_num

private theorem prime_oneHundredTwentyNineDW_22670311 : Nat.Prime 22670311 := by norm_num

private theorem prime_oneHundredTwentyNineDW_23182517 : Nat.Prime 23182517 := by norm_num

private theorem prime_oneHundredTwentyNineDW_23496937 : Nat.Prime 23496937 := by norm_num

private theorem prime_oneHundredTwentyNineDW_24098993 : Nat.Prime 24098993 := by norm_num

private theorem prime_oneHundredTwentyNineDW_25181489 : Nat.Prime 25181489 := by norm_num

private theorem prime_oneHundredTwentyNineDW_25240343 : Nat.Prime 25240343 := by norm_num

private theorem prime_oneHundredTwentyNineDW_25389829 : Nat.Prime 25389829 := by norm_num

private theorem prime_oneHundredTwentyNineDW_26594759 : Nat.Prime 26594759 := by norm_num

private theorem prime_oneHundredTwentyNineDW_27235337 : Nat.Prime 27235337 := by norm_num

private theorem prime_oneHundredTwentyNineDW_27695231 : Nat.Prime 27695231 := by norm_num

private theorem prime_oneHundredTwentyNineDW_28349813 : Nat.Prime 28349813 := by norm_num

private theorem prime_oneHundredTwentyNineDW_28500727 : Nat.Prime 28500727 := by norm_num

private theorem prime_oneHundredTwentyNineDW_31279981 : Nat.Prime 31279981 := by
  apply lucas_primality 31279981 (2 : ZMod 31279981)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (17977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (17977, 1)] : List FactorBlock).map factorBlockValue).prod) = 31279981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_17977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31279981) ^ 15639990 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31279981) ^ 10426660 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31279981) ^ 6255996 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31279981) ^ 1078620 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 31279981) ^ 1740 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_33085331 : Nat.Prime 33085331 := by
  apply lucas_primality 33085331 (2 : ZMod 33085331)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3308533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3308533, 1)] : List FactorBlock).map factorBlockValue).prod) = 33085331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_3308533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33085331) ^ 16542665 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33085331) ^ 6617066 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 33085331) ^ 10 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_34201267 : Nat.Prime 34201267 := by
  apply lucas_primality 34201267 (3 : ZMod 34201267)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (29, 1), (107, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (29, 1), (107, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 34201267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_107
      · exact prime_oneHundredTwentyNineDW_167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34201267) ^ 17100633 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 34201267) ^ 11400422 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 34201267) ^ 3109206 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 34201267) ^ 1179354 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 34201267) ^ 319638 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 34201267) ^ 204798 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_36323929 : Nat.Prime 36323929 := by
  apply lucas_primality 36323929 (14 : ZMod 36323929)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (613, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (613, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 36323929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_613
      · exact prime_oneHundredTwentyNineDW_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 36323929) ^ 18161964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 36323929) ^ 12107976 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 36323929) ^ 59256 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 36323929) ^ 44136 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_38618497 : Nat.Prime 38618497 := by
  apply lucas_primality 38618497 (10 : ZMod 38618497)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (7, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (7, 1), (4789, 1)] : List FactorBlock).map factorBlockValue).prod) = 38618497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_4789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 38618497) ^ 19309248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 38618497) ^ 12872832 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 38618497) ^ 5516928 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 38618497) ^ 8064 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_40719037 : Nat.Prime 40719037 := by
  apply lucas_primality 40719037 (6 : ZMod 40719037)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (337, 1), (10069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (337, 1), (10069, 1)] : List FactorBlock).map factorBlockValue).prod) = 40719037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_337
      · exact prime_oneHundredTwentyNineDW_10069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 40719037) ^ 20359518 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 40719037) ^ 13573012 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 40719037) ^ 120828 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 40719037) ^ 4044 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_54283751 : Nat.Prime 54283751 := by
  apply lucas_primality 54283751 (11 : ZMod 54283751)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (43427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (43427, 1)] : List FactorBlock).map factorBlockValue).prod) = 54283751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_43427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 54283751) ^ 27141875 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54283751) ^ 10856750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 54283751) ^ 1250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_61073849 : Nat.Prime 61073849 := by
  apply lucas_primality 61073849 (3 : ZMod 61073849)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (523, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (523, 1), (1327, 1)] : List FactorBlock).map factorBlockValue).prod) = 61073849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_523
      · exact prime_oneHundredTwentyNineDW_1327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61073849) ^ 30536924 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61073849) ^ 5552168 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61073849) ^ 116776 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61073849) ^ 46024 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_61131197 : Nat.Prime 61131197 := by
  apply lucas_primality 61131197 (3 : ZMod 61131197)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (127, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (127, 1), (17191, 1)] : List FactorBlock).map factorBlockValue).prod) = 61131197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_127
      · exact prime_oneHundredTwentyNineDW_17191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61131197) ^ 30565598 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61131197) ^ 8733028 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61131197) ^ 481348 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61131197) ^ 3556 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_62457911 : Nat.Prime 62457911 := by
  apply lucas_primality 62457911 (19 : ZMod 62457911)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6245791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6245791, 1)] : List FactorBlock).map factorBlockValue).prod) = 62457911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_6245791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 62457911) ^ 31228955 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 62457911) ^ 12491582 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 62457911) ^ 10 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_65391373 : Nat.Prime 65391373 := by
  apply lucas_primality 65391373 (5 : ZMod 65391373)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (673, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (673, 1), (2699, 1)] : List FactorBlock).map factorBlockValue).prod) = 65391373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_673
      · exact prime_oneHundredTwentyNineDW_2699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 65391373) ^ 32695686 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 65391373) ^ 21797124 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 65391373) ^ 97164 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 65391373) ^ 24228 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_67841003 : Nat.Prime 67841003 := by
  apply lucas_primality 67841003 (2 : ZMod 67841003)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3389, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3389, 1), (10009, 1)] : List FactorBlock).map factorBlockValue).prod) = 67841003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3389
      · exact prime_oneHundredTwentyNineDW_10009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67841003) ^ 33920501 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67841003) ^ 20018 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67841003) ^ 6778 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_69453511 : Nat.Prime 69453511 := by
  apply lucas_primality 69453511 (3 : ZMod 69453511)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (330731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (330731, 1)] : List FactorBlock).map factorBlockValue).prod) = 69453511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_330731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 69453511) ^ 34726755 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 69453511) ^ 23151170 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 69453511) ^ 13890702 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 69453511) ^ 9921930 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 69453511) ^ 210 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_72021127 : Nat.Prime 72021127 := by
  apply lucas_primality 72021127 (21 : ZMod 72021127)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3413, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3413, 1), (3517, 1)] : List FactorBlock).map factorBlockValue).prod) = 72021127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_3413
      · exact prime_oneHundredTwentyNineDW_3517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (21 : ZMod 72021127) ^ 36010563 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (21 : ZMod 72021127) ^ 24007042 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (21 : ZMod 72021127) ^ 21102 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (21 : ZMod 72021127) ^ 20478 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_73009591 : Nat.Prime 73009591 := by
  apply lucas_primality 73009591 (7 : ZMod 73009591)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (23, 1), (5569, 1)] : List FactorBlock).map factorBlockValue).prod) = 73009591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_5569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 73009591) ^ 36504795 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73009591) ^ 24336530 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73009591) ^ 14601918 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73009591) ^ 3842610 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73009591) ^ 3174330 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73009591) ^ 13110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_74050117 : Nat.Prime 74050117 := by
  apply lucas_primality 74050117 (2 : ZMod 74050117)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (16633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (16633, 1)] : List FactorBlock).map factorBlockValue).prod) = 74050117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_16633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74050117) ^ 37025058 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74050117) ^ 24683372 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74050117) ^ 10578588 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74050117) ^ 1397172 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 74050117) ^ 4452 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_86102881 : Nat.Prime 86102881 := by
  apply lucas_primality 86102881 (11 : ZMod 86102881)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (179381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (179381, 1)] : List FactorBlock).map factorBlockValue).prod) = 86102881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_179381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 86102881) ^ 43051440 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 86102881) ^ 28700960 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 86102881) ^ 17220576 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 86102881) ^ 480 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_88073779 : Nat.Prime 88073779 := by
  apply lucas_primality 88073779 (3 : ZMod 88073779)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (67, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (67, 1), (887, 1)] : List FactorBlock).map factorBlockValue).prod) = 88073779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_67
      · exact prime_oneHundredTwentyNineDW_887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88073779) ^ 44036889 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88073779) ^ 29357926 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88073779) ^ 6774906 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88073779) ^ 4635462 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88073779) ^ 1314534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 88073779) ^ 99294 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_88588699 : Nat.Prime 88588699 := by
  apply lucas_primality 88588699 (10 : ZMod 88588699)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 3), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 3), (11093, 1)] : List FactorBlock).map factorBlockValue).prod) = 88588699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_11093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 88588699) ^ 44294349 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 88588699) ^ 29529566 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 88588699) ^ 8053518 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 88588699) ^ 7986 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_96011117 : Nat.Prime 96011117 := by
  apply lucas_primality 96011117 (2 : ZMod 96011117)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (125669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (125669, 1)] : List FactorBlock).map factorBlockValue).prod) = 96011117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_191
      · exact prime_oneHundredTwentyNineDW_125669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96011117) ^ 48005558 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 96011117) ^ 502676 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 96011117) ^ 764 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_98178361 : Nat.Prime 98178361 := by
  apply lucas_primality 98178361 (13 : ZMod 98178361)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 2), (59, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 2), (59, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 98178361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_59
      · exact prime_oneHundredTwentyNineDW_283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 98178361) ^ 49089180 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 98178361) ^ 32726120 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 98178361) ^ 19635672 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 98178361) ^ 14025480 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 98178361) ^ 1664040 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 98178361) ^ 346920 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_101564531 : Nat.Prime 101564531 := by
  apply lucas_primality 101564531 (2 : ZMod 101564531)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (181, 1), (56113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (181, 1), (56113, 1)] : List FactorBlock).map factorBlockValue).prod) = 101564531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_181
      · exact prime_oneHundredTwentyNineDW_56113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101564531) ^ 50782265 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101564531) ^ 20312906 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101564531) ^ 561130 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101564531) ^ 1810 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_116357179 : Nat.Prime 116357179 := by
  apply lucas_primality 116357179 (2 : ZMod 116357179)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (139, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (139, 1), (1049, 1)] : List FactorBlock).map factorBlockValue).prod) = 116357179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_139
      · exact prime_oneHundredTwentyNineDW_1049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116357179) ^ 58178589 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116357179) ^ 38785726 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116357179) ^ 16622454 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116357179) ^ 6124062 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116357179) ^ 837102 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 116357179) ^ 110922 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_124176583 : Nat.Prime 124176583 := by
  apply lucas_primality 124176583 (3 : ZMod 124176583)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (769, 1), (8971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (769, 1), (8971, 1)] : List FactorBlock).map factorBlockValue).prod) = 124176583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_769
      · exact prime_oneHundredTwentyNineDW_8971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 124176583) ^ 62088291 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 124176583) ^ 41392194 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 124176583) ^ 161478 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 124176583) ^ 13842 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_125928779 : Nat.Prime 125928779 := by
  apply lucas_primality 125928779 (2 : ZMod 125928779)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (939767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (939767, 1)] : List FactorBlock).map factorBlockValue).prod) = 125928779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_67
      · exact prime_oneHundredTwentyNineDW_939767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 125928779) ^ 62964389 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 125928779) ^ 1879534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 125928779) ^ 134 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_146147093 : Nat.Prime 146147093 := by
  apply lucas_primality 146147093 (5 : ZMod 146147093)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (331, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (331, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 146147093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_331
      · exact prime_oneHundredTwentyNineDW_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 146147093) ^ 73073546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 146147093) ^ 20878156 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 146147093) ^ 11242084 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 146147093) ^ 441532 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 146147093) ^ 120484 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_161382281 : Nat.Prime 161382281 := by
  apply lucas_primality 161382281 (3 : ZMod 161382281)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (31, 1), (130147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (31, 1), (130147, 1)] : List FactorBlock).map factorBlockValue).prod) = 161382281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_130147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 161382281) ^ 80691140 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 161382281) ^ 32276456 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 161382281) ^ 5205880 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 161382281) ^ 1240 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_183681881 : Nat.Prime 183681881 := by
  apply lucas_primality 183681881 (3 : ZMod 183681881)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (929, 1), (4943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (929, 1), (4943, 1)] : List FactorBlock).map factorBlockValue).prod) = 183681881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_929
      · exact prime_oneHundredTwentyNineDW_4943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 183681881) ^ 91840940 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183681881) ^ 36736376 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183681881) ^ 197720 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 183681881) ^ 37160 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_189251033 : Nat.Prime 189251033 := by
  apply lucas_primality 189251033 (3 : ZMod 189251033)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (109, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (109, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) = 189251033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_109
      · exact prime_oneHundredTwentyNineDW_7001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 189251033) ^ 94625516 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 189251033) ^ 6104872 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 189251033) ^ 1736248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 189251033) ^ 27032 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_218057183 : Nat.Prime 218057183 := by
  apply lucas_primality 218057183 (7 : ZMod 218057183)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (101, 1), (154213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (101, 1), (154213, 1)] : List FactorBlock).map factorBlockValue).prod) = 218057183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_101
      · exact prime_oneHundredTwentyNineDW_154213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 218057183) ^ 109028591 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 218057183) ^ 31151026 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 218057183) ^ 2158982 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 218057183) ^ 1414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_225854353 : Nat.Prime 225854353 := by
  apply lucas_primality 225854353 (5 : ZMod 225854353)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (522811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (522811, 1)] : List FactorBlock).map factorBlockValue).prod) = 225854353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_522811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 225854353) ^ 112927176 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 225854353) ^ 75284784 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 225854353) ^ 432 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_226640737 : Nat.Prime 226640737 := by
  apply lucas_primality 226640737 (5 : ZMod 226640737)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (7, 1), (17, 2), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (7, 1), (17, 2), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 226640737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 226640737) ^ 113320368 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 226640737) ^ 75546912 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 226640737) ^ 32377248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 226640737) ^ 13331808 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 226640737) ^ 582624 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_269498197 : Nat.Prime 269498197 := by
  apply lucas_primality 269498197 (15 : ZMod 269498197)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (617, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (617, 1), (1103, 1)] : List FactorBlock).map factorBlockValue).prod) = 269498197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_617
      · exact prime_oneHundredTwentyNineDW_1103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 269498197) ^ 134749098 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 269498197) ^ 89832732 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 269498197) ^ 24499836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 269498197) ^ 436788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 269498197) ^ 244332 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_278788001 : Nat.Prime 278788001 := by
  apply lucas_primality 278788001 (3 : ZMod 278788001)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 3), (69697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 3), (69697, 1)] : List FactorBlock).map factorBlockValue).prod) = 278788001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_69697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 278788001) ^ 139394000 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 278788001) ^ 55757600 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 278788001) ^ 4000 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_283484081 : Nat.Prime 283484081 := by
  apply lucas_primality 283484081 (3 : ZMod 283484081)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (61, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (61, 1), (5281, 1)] : List FactorBlock).map factorBlockValue).prod) = 283484081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_61
      · exact prime_oneHundredTwentyNineDW_5281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 283484081) ^ 141742040 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283484081) ^ 56696816 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283484081) ^ 25771280 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283484081) ^ 4647280 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 283484081) ^ 53680 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_288684659 : Nat.Prime 288684659 := by
  apply lucas_primality 288684659 (2 : ZMod 288684659)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (755719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (755719, 1)] : List FactorBlock).map factorBlockValue).prod) = 288684659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_191
      · exact prime_oneHundredTwentyNineDW_755719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 288684659) ^ 144342329 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 288684659) ^ 1511438 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 288684659) ^ 382 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_296403397 : Nat.Prime 296403397 := by
  apply lucas_primality 296403397 (2 : ZMod 296403397)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1187, 1), (20809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1187, 1), (20809, 1)] : List FactorBlock).map factorBlockValue).prod) = 296403397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_1187
      · exact prime_oneHundredTwentyNineDW_20809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 296403397) ^ 148201698 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 296403397) ^ 98801132 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 296403397) ^ 249708 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 296403397) ^ 14244 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_302884117 : Nat.Prime 302884117 := by
  apply lucas_primality 302884117 (2 : ZMod 302884117)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (25240343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (25240343, 1)] : List FactorBlock).map factorBlockValue).prod) = 302884117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_25240343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 302884117) ^ 151442058 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 302884117) ^ 100961372 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 302884117) ^ 12 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_305463187 : Nat.Prime 305463187 := by
  apply lucas_primality 305463187 (3 : ZMod 305463187)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (103, 1), (23537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (103, 1), (23537, 1)] : List FactorBlock).map factorBlockValue).prod) = 305463187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_103
      · exact prime_oneHundredTwentyNineDW_23537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 305463187) ^ 152731593 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 305463187) ^ 101821062 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 305463187) ^ 43637598 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 305463187) ^ 2965662 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 305463187) ^ 12978 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_341046383 : Nat.Prime 341046383 := by
  apply lucas_primality 341046383 (5 : ZMod 341046383)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (3628153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (3628153, 1)] : List FactorBlock).map factorBlockValue).prod) = 341046383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_3628153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 341046383) ^ 170523191 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 341046383) ^ 7256306 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 341046383) ^ 94 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_342889753 : Nat.Prime 342889753 := by
  apply lucas_primality 342889753 (5 : ZMod 342889753)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (14287073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (14287073, 1)] : List FactorBlock).map factorBlockValue).prod) = 342889753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_14287073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 342889753) ^ 171444876 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 342889753) ^ 114296584 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 342889753) ^ 24 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_348529057 : Nat.Prime 348529057 := by
  apply lucas_primality 348529057 (10 : ZMod 348529057)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (1277, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (1277, 1), (2843, 1)] : List FactorBlock).map factorBlockValue).prod) = 348529057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_1277
      · exact prime_oneHundredTwentyNineDW_2843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 348529057) ^ 174264528 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 348529057) ^ 116176352 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 348529057) ^ 272928 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 348529057) ^ 122592 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_374747467 : Nat.Prime 374747467 := by
  apply lucas_primality 374747467 (2 : ZMod 374747467)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (62457911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (62457911, 1)] : List FactorBlock).map factorBlockValue).prod) = 374747467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_62457911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 374747467) ^ 187373733 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 374747467) ^ 124915822 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 374747467) ^ 6 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_378502067 : Nat.Prime 378502067 := by
  apply lucas_primality 378502067 (2 : ZMod 378502067)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (189251033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (189251033, 1)] : List FactorBlock).map factorBlockValue).prod) = 378502067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_189251033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 378502067) ^ 189251033 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 378502067) ^ 2 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_384202751 : Nat.Prime 384202751 := by
  apply lucas_primality 384202751 (7 : ZMod 384202751)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1536811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1536811, 1)] : List FactorBlock).map factorBlockValue).prod) = 384202751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_1536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 384202751) ^ 192101375 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 384202751) ^ 76840550 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 384202751) ^ 250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_399713417 : Nat.Prime 399713417 := by
  apply lucas_primality 399713417 (3 : ZMod 399713417)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3613, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3613, 1), (13829, 1)] : List FactorBlock).map factorBlockValue).prod) = 399713417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3613
      · exact prime_oneHundredTwentyNineDW_13829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 399713417) ^ 199856708 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 399713417) ^ 110632 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 399713417) ^ 28904 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_409269811 : Nat.Prime 409269811 := by
  apply lucas_primality 409269811 (3 : ZMod 409269811)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13642327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13642327, 1)] : List FactorBlock).map factorBlockValue).prod) = 409269811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_13642327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 409269811) ^ 204634905 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 409269811) ^ 136423270 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 409269811) ^ 81853962 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 409269811) ^ 30 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_426295189 : Nat.Prime 426295189 := by
  apply lucas_primality 426295189 (6 : ZMod 426295189)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (1076503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (1076503, 1)] : List FactorBlock).map factorBlockValue).prod) = 426295189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_1076503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 426295189) ^ 213147594 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 426295189) ^ 142098396 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 426295189) ^ 38754108 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 426295189) ^ 396 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_489049577 : Nat.Prime 489049577 := by
  apply lucas_primality 489049577 (3 : ZMod 489049577)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61131197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61131197, 1)] : List FactorBlock).map factorBlockValue).prod) = 489049577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_61131197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 489049577) ^ 244524788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 489049577) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_530487563 : Nat.Prime 530487563 := by
  apply lucas_primality 530487563 (2 : ZMod 530487563)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (31, 1), (40939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (31, 1), (40939, 1)] : List FactorBlock).map factorBlockValue).prod) = 530487563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_40939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 530487563) ^ 265243781 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530487563) ^ 48226142 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530487563) ^ 27920398 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530487563) ^ 17112502 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 530487563) ^ 12958 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_616415557 : Nat.Prime 616415557 := by
  apply lucas_primality 616415557 (5 : ZMod 616415557)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (2703577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (2703577, 1)] : List FactorBlock).map factorBlockValue).prod) = 616415557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_2703577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 616415557) ^ 308207778 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 616415557) ^ 205471852 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 616415557) ^ 32442924 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 616415557) ^ 228 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_61
      · exact prime_oneHundredTwentyNineDW_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_661471427 : Nat.Prime 661471427 := by
  apply lucas_primality 661471427 (2 : ZMod 661471427)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 2), (390479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 2), (390479, 1)] : List FactorBlock).map factorBlockValue).prod) = 661471427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_390479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 661471427) ^ 330735713 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 661471427) ^ 94495918 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 661471427) ^ 60133766 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 661471427) ^ 1694 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17203
      · exact prime_oneHundredTwentyNineDW_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_768405503 : Nat.Prime 768405503 := by
  apply lucas_primality 768405503 (5 : ZMod 768405503)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (384202751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (384202751, 1)] : List FactorBlock).map factorBlockValue).prod) = 768405503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_384202751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 768405503) ^ 384202751 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 768405503) ^ 2 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_781910413 : Nat.Prime 781910413 := by
  apply lucas_primality 781910413 (5 : ZMod 781910413)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (2246869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (2246869, 1)] : List FactorBlock).map factorBlockValue).prod) = 781910413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_2246869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 781910413) ^ 390955206 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 781910413) ^ 260636804 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 781910413) ^ 26962428 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 781910413) ^ 348 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_795729673 : Nat.Prime 795729673 := by
  apply lucas_primality 795729673 (5 : ZMod 795729673)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11051801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11051801, 1)] : List FactorBlock).map factorBlockValue).prod) = 795729673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11051801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 795729673) ^ 397864836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 795729673) ^ 265243224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 795729673) ^ 72 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_875303903 : Nat.Prime 875303903 := by
  apply lucas_primality 875303903 (5 : ZMod 875303903)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (311, 1), (127931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (311, 1), (127931, 1)] : List FactorBlock).map factorBlockValue).prod) = 875303903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_311
      · exact prime_oneHundredTwentyNineDW_127931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 875303903) ^ 437651951 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 875303903) ^ 79573082 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 875303903) ^ 2814482 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 875303903) ^ 6842 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_961180807 : Nat.Prime 961180807 := by
  apply lucas_primality 961180807 (3 : ZMod 961180807)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (3725507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (3725507, 1)] : List FactorBlock).map factorBlockValue).prod) = 961180807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_43
      · exact prime_oneHundredTwentyNineDW_3725507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 961180807) ^ 480590403 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 961180807) ^ 320393602 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 961180807) ^ 22353042 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 961180807) ^ 258 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1000639879 : Nat.Prime 1000639879 := by
  apply lucas_primality 1000639879 (3 : ZMod 1000639879)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (419, 1), (8123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (419, 1), (8123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1000639879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_419
      · exact prime_oneHundredTwentyNineDW_8123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1000639879) ^ 500319939 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1000639879) ^ 333546626 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1000639879) ^ 142948554 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1000639879) ^ 2388162 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1000639879) ^ 123186 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1035604699 : Nat.Prime 1035604699 := by
  apply lucas_primality 1035604699 (3 : ZMod 1035604699)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (2925437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (2925437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1035604699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_59
      · exact prime_oneHundredTwentyNineDW_2925437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1035604699) ^ 517802349 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1035604699) ^ 345201566 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1035604699) ^ 17552622 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1035604699) ^ 354 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1060975127 : Nat.Prime 1060975127 := by
  apply lucas_primality 1060975127 (5 : ZMod 1060975127)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (530487563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (530487563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1060975127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_530487563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1060975127) ^ 530487563 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1060975127) ^ 2 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1069936841 : Nat.Prime 1069936841 := by
  apply lucas_primality 1069936841 (3 : ZMod 1069936841)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (3821203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (3821203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1069936841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_3821203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1069936841) ^ 534968420 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069936841) ^ 213987368 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069936841) ^ 152848120 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1069936841) ^ 280 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1077992789 : Nat.Prime 1077992789 := by
  apply lucas_primality 1077992789 (2 : ZMod 1077992789)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (269498197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (269498197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1077992789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_269498197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1077992789) ^ 538996394 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1077992789) ^ 4 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1109688469 : Nat.Prime 1109688469 := by
  apply lucas_primality 1109688469 (2 : ZMod 1109688469)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (13210577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (13210577, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109688469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13210577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1109688469) ^ 554844234 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109688469) ^ 369896156 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109688469) ^ 158526924 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109688469) ^ 84 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1166223829 : Nat.Prime 1166223829 := by
  apply lucas_primality 1166223829 (6 : ZMod 1166223829)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (1262147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (1262147, 1)] : List FactorBlock).map factorBlockValue).prod) = 1166223829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_1262147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1166223829) ^ 583111914 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1166223829) ^ 388741276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1166223829) ^ 166603404 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1166223829) ^ 106020348 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1166223829) ^ 924 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1246239409 : Nat.Prime 1246239409 := by
  apply lucas_primality 1246239409 (11 : ZMod 1246239409)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (173, 1), (150077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (173, 1), (150077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1246239409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_173
      · exact prime_oneHundredTwentyNineDW_150077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1246239409) ^ 623119704 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1246239409) ^ 415413136 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1246239409) ^ 7203696 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 1246239409) ^ 8304 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1296380287 : Nat.Prime 1296380287 := by
  apply lucas_primality 1296380287 (3 : ZMod 1296380287)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (72021127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (72021127, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296380287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_72021127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1296380287) ^ 648190143 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1296380287) ^ 432126762 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1296380287) ^ 18 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1469455049 : Nat.Prime 1469455049 := by
  apply lucas_primality 1469455049 (3 : ZMod 1469455049)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (183681881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (183681881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1469455049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_183681881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1469455049) ^ 734727524 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1469455049) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1470404993 : Nat.Prime 1470404993 := by
  apply lucas_primality 1470404993 (3 : ZMod 1470404993)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (7, 1), (1641077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (7, 1), (1641077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1470404993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_1641077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1470404993) ^ 735202496 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1470404993) ^ 210057856 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1470404993) ^ 896 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1511273629 : Nat.Prime 1511273629 := by
  apply lucas_primality 1511273629 (2 : ZMod 1511273629)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (83, 1), (505781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (83, 1), (505781, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511273629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_83
      · exact prime_oneHundredTwentyNineDW_505781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1511273629) ^ 755636814 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1511273629) ^ 503757876 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1511273629) ^ 18208116 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1511273629) ^ 2988 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2126128777 : Nat.Prime 2126128777 := by
  apply lucas_primality 2126128777 (7 : ZMod 2126128777)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (88588699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (88588699, 1)] : List FactorBlock).map factorBlockValue).prod) = 2126128777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_88588699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2126128777) ^ 1063064388 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2126128777) ^ 708709592 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 2126128777) ^ 24 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2128057391 : Nat.Prime 2128057391 := by
  apply lucas_primality 2128057391 (11 : ZMod 2128057391)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (12569, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (12569, 1), (16931, 1)] : List FactorBlock).map factorBlockValue).prod) = 2128057391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_12569
      · exact prime_oneHundredTwentyNineDW_16931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 2128057391) ^ 1064028695 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128057391) ^ 425611478 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128057391) ^ 169310 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2128057391) ^ 125690 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2236316317 : Nat.Prime 2236316317 := by
  apply lucas_primality 2236316317 (15 : ZMod 2236316317)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (163, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (163, 1), (2837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2236316317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_163
      · exact prime_oneHundredTwentyNineDW_2837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 2236316317) ^ 1118158158 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 2236316317) ^ 745438772 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 2236316317) ^ 172024332 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 2236316317) ^ 72139236 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 2236316317) ^ 13719732 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 2236316317) ^ 788268 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2279917543 : Nat.Prime 2279917543 := by
  apply lucas_primality 2279917543 (6 : ZMod 2279917543)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (54283751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (54283751, 1)] : List FactorBlock).map factorBlockValue).prod) = 2279917543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_54283751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2279917543) ^ 1139958771 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2279917543) ^ 759972514 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2279917543) ^ 325702506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2279917543) ^ 42 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2558864369 : Nat.Prime 2558864369 := by
  apply lucas_primality 2558864369 (3 : ZMod 2558864369)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (1489, 1), (5653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (1489, 1), (5653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2558864369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_1489
      · exact prime_oneHundredTwentyNineDW_5653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2558864369) ^ 1279432184 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2558864369) ^ 134677072 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2558864369) ^ 1718512 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2558864369) ^ 452656 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2690395889 : Nat.Prime 2690395889 := by
  apply lucas_primality 2690395889 (3 : ZMod 2690395889)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (5798267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (5798267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2690395889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_5798267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2690395889) ^ 1345197944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2690395889) ^ 92772272 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 2690395889) ^ 464 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3062600461 : Nat.Prime 3062600461 := by
  apply lucas_primality 3062600461 (6 : ZMod 3062600461)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (379, 1), (44893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (379, 1), (44893, 1)] : List FactorBlock).map factorBlockValue).prod) = 3062600461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_379
      · exact prime_oneHundredTwentyNineDW_44893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3062600461) ^ 1531300230 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3062600461) ^ 1020866820 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3062600461) ^ 612520092 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3062600461) ^ 8080740 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3062600461) ^ 68220 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3095912461 : Nat.Prime 3095912461 := by
  apply lucas_primality 3095912461 (2 : ZMod 3095912461)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (41, 1), (283, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (41, 1), (283, 1), (4447, 1)] : List FactorBlock).map factorBlockValue).prod) = 3095912461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_283
      · exact prime_oneHundredTwentyNineDW_4447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3095912461) ^ 1547956230 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095912461) ^ 1031970820 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095912461) ^ 619182492 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095912461) ^ 75510060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095912461) ^ 10939620 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095912461) ^ 696180 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3599356037 : Nat.Prime 3599356037 := by
  apply lucas_primality 3599356037 (2 : ZMod 3599356037)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (191, 1), (397, 1), (11867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (191, 1), (397, 1), (11867, 1)] : List FactorBlock).map factorBlockValue).prod) = 3599356037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_191
      · exact prime_oneHundredTwentyNineDW_397
      · exact prime_oneHundredTwentyNineDW_11867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3599356037) ^ 1799678018 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3599356037) ^ 18844796 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3599356037) ^ 9066388 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3599356037) ^ 303308 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3603525251 : Nat.Prime 3603525251 := by
  apply lucas_primality 3603525251 (2 : ZMod 3603525251)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (13, 1), (31, 1), (47, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (13, 1), (31, 1), (47, 1), (761, 1)] : List FactorBlock).map factorBlockValue).prod) = 3603525251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3603525251) ^ 1801762625 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3603525251) ^ 720705050 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3603525251) ^ 277194250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3603525251) ^ 116242750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3603525251) ^ 76670750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3603525251) ^ 4735250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3613669649 : Nat.Prime 3613669649 := by
  apply lucas_primality 3613669649 (3 : ZMod 3613669649)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (225854353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (225854353, 1)] : List FactorBlock).map factorBlockValue).prod) = 3613669649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_225854353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3613669649) ^ 1806834824 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 3613669649) ^ 16 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4025867683 : Nat.Prime 4025867683 := by
  apply lucas_primality 4025867683 (2 : ZMod 4025867683)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (103, 1), (22541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (103, 1), (22541, 1)] : List FactorBlock).map factorBlockValue).prod) = 4025867683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_103
      · exact prime_oneHundredTwentyNineDW_22541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4025867683) ^ 2012933841 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4025867683) ^ 1341955894 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4025867683) ^ 236815746 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4025867683) ^ 39086094 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4025867683) ^ 178602 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4149352969 : Nat.Prime 4149352969 := by
  apply lucas_primality 4149352969 (13 : ZMod 4149352969)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4889, 1), (35363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4889, 1), (35363, 1)] : List FactorBlock).map factorBlockValue).prod) = 4149352969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_4889
      · exact prime_oneHundredTwentyNineDW_35363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4149352969) ^ 2074676484 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 4149352969) ^ 1383117656 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 4149352969) ^ 848712 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 4149352969) ^ 117336 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4428013127 : Nat.Prime 4428013127 := by
  apply lucas_primality 4428013127 (5 : ZMod 4428013127)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33829, 1), (65447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33829, 1), (65447, 1)] : List FactorBlock).map factorBlockValue).prod) = 4428013127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_33829
      · exact prime_oneHundredTwentyNineDW_65447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4428013127) ^ 2214006563 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4428013127) ^ 130894 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4428013127) ^ 67658 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4833910351 : Nat.Prime 4833910351 := by
  apply lucas_primality 4833910351 (15 : ZMod 4833910351)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (73, 1), (147151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (73, 1), (147151, 1)] : List FactorBlock).map factorBlockValue).prod) = 4833910351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_73
      · exact prime_oneHundredTwentyNineDW_147151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 4833910351) ^ 2416955175 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4833910351) ^ 1611303450 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4833910351) ^ 966782070 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4833910351) ^ 66217950 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (15 : ZMod 4833910351) ^ 32850 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5103381739 : Nat.Prime 5103381739 := by
  apply lucas_primality 5103381739 (2 : ZMod 5103381739)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (9346853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (9346853, 1)] : List FactorBlock).map factorBlockValue).prod) = 5103381739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_9346853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5103381739) ^ 2551690869 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5103381739) ^ 1701127246 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5103381739) ^ 729054534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5103381739) ^ 392567826 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5103381739) ^ 546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5185521149 : Nat.Prime 5185521149 := by
  apply lucas_primality 5185521149 (2 : ZMod 5185521149)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1296380287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1296380287, 1)] : List FactorBlock).map factorBlockValue).prod) = 5185521149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_1296380287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5185521149) ^ 2592760574 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5185521149) ^ 4 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5682790147 : Nat.Prime 5682790147 := by
  apply lucas_primality 5682790147 (2 : ZMod 5682790147)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (86102881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (86102881, 1)] : List FactorBlock).map factorBlockValue).prod) = 5682790147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_86102881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5682790147) ^ 2841395073 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5682790147) ^ 1894263382 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5682790147) ^ 516617286 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 5682790147) ^ 66 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6277150273 : Nat.Prime 6277150273 := by
  apply lucas_primality 6277150273 (5 : ZMod 6277150273)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (503, 1), (64997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (503, 1), (64997, 1)] : List FactorBlock).map factorBlockValue).prod) = 6277150273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_503
      · exact prime_oneHundredTwentyNineDW_64997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6277150273) ^ 3138575136 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277150273) ^ 2092383424 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277150273) ^ 12479424 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6277150273) ^ 96576 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_7364218699 : Nat.Prime 7364218699 := by
  apply lucas_primality 7364218699 (2 : ZMod 7364218699)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (127, 1), (3221443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (127, 1), (3221443, 1)] : List FactorBlock).map factorBlockValue).prod) = 7364218699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_127
      · exact prime_oneHundredTwentyNineDW_3221443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7364218699) ^ 3682109349 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7364218699) ^ 2454739566 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7364218699) ^ 57985974 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7364218699) ^ 2286 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_8727780323 : Nat.Prime 8727780323 := by
  apply lucas_primality 8727780323 (2 : ZMod 8727780323)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (38618497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (38618497, 1)] : List FactorBlock).map factorBlockValue).prod) = 8727780323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_113
      · exact prime_oneHundredTwentyNineDW_38618497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8727780323) ^ 4363890161 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8727780323) ^ 77236994 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8727780323) ^ 226 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_8945265269 : Nat.Prime 8945265269 := by
  apply lucas_primality 8945265269 (2 : ZMod 8945265269)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2236316317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2236316317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8945265269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_2236316317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8945265269) ^ 4472632634 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 8945265269) ^ 4 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_9343936853 : Nat.Prime 9343936853 := by
  apply lucas_primality 9343936853 (2 : ZMod 9343936853)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (101564531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (101564531, 1)] : List FactorBlock).map factorBlockValue).prod) = 9343936853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_101564531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9343936853) ^ 4671968426 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9343936853) ^ 406258124 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9343936853) ^ 92 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_10377571691 : Nat.Prime 10377571691 := by
  apply lucas_primality 10377571691 (2 : ZMod 10377571691)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (10949, 1), (94781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (10949, 1), (94781, 1)] : List FactorBlock).map factorBlockValue).prod) = 10377571691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_10949
      · exact prime_oneHundredTwentyNineDW_94781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10377571691) ^ 5188785845 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10377571691) ^ 2075514338 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10377571691) ^ 947810 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10377571691) ^ 109490 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_10492929077 : Nat.Prime 10492929077 := by
  apply lucas_primality 10492929077 (2 : ZMod 10492929077)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (374747467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (374747467, 1)] : List FactorBlock).map factorBlockValue).prod) = 10492929077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_374747467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10492929077) ^ 5246464538 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10492929077) ^ 1498989868 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10492929077) ^ 28 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_10957916839 : Nat.Prime 10957916839 := by
  apply lucas_primality 10957916839 (6 : ZMod 10957916839)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (233, 1), (712571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (233, 1), (712571, 1)] : List FactorBlock).map factorBlockValue).prod) = 10957916839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_233
      · exact prime_oneHundredTwentyNineDW_712571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10957916839) ^ 5478958419 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10957916839) ^ 3652638946 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10957916839) ^ 996174258 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10957916839) ^ 47029686 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 10957916839) ^ 15378 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_11204590099 : Nat.Prime 11204590099 := by
  apply lucas_primality 11204590099 (2 : ZMod 11204590099)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (47, 1), (3056353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (47, 1), (3056353, 1)] : List FactorBlock).map factorBlockValue).prod) = 11204590099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_3056353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11204590099) ^ 5602295049 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11204590099) ^ 3734863366 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11204590099) ^ 861891546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11204590099) ^ 238395534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11204590099) ^ 3666 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_14386102061 : Nat.Prime 14386102061 := by
  apply lucas_primality 14386102061 (2 : ZMod 14386102061)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (65391373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (65391373, 1)] : List FactorBlock).map factorBlockValue).prod) = 14386102061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_65391373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14386102061) ^ 7193051030 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14386102061) ^ 2877220412 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14386102061) ^ 1307827460 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14386102061) ^ 220 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_20470914953 : Nat.Prime 20470914953 := by
  apply lucas_primality 20470914953 (3 : ZMod 20470914953)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2558864369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2558864369, 1)] : List FactorBlock).map factorBlockValue).prod) = 20470914953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_2558864369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20470914953) ^ 10235457476 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 20470914953) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_20595930307 : Nat.Prime 20595930307 := by
  apply lucas_primality 20595930307 (2 : ZMod 20595930307)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (443, 1), (487, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (443, 1), (487, 1), (2273, 1)] : List FactorBlock).map factorBlockValue).prod) = 20595930307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_443
      · exact prime_oneHundredTwentyNineDW_487
      · exact prime_oneHundredTwentyNineDW_2273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20595930307) ^ 10297965153 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20595930307) ^ 6865310102 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20595930307) ^ 2942275758 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20595930307) ^ 46491942 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20595930307) ^ 42291438 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 20595930307) ^ 9061122 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_21291945497 : Nat.Prime 21291945497 := by
  apply lucas_primality 21291945497 (3 : ZMod 21291945497)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (139, 1), (19147433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (139, 1), (19147433, 1)] : List FactorBlock).map factorBlockValue).prod) = 21291945497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_139
      · exact prime_oneHundredTwentyNineDW_19147433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 21291945497) ^ 10645972748 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21291945497) ^ 153179464 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 21291945497) ^ 1112 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_22090552511 : Nat.Prime 22090552511 := by
  apply lucas_primality 22090552511 (11 : ZMod 22090552511)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (29, 1), (239, 1), (24517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (29, 1), (239, 1), (24517, 1)] : List FactorBlock).map factorBlockValue).prod) = 22090552511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_239
      · exact prime_oneHundredTwentyNineDW_24517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22090552511) ^ 11045276255 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 22090552511) ^ 4418110502 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 22090552511) ^ 1699273270 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 22090552511) ^ 761743190 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 22090552511) ^ 92429090 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 22090552511) ^ 901030 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_23754127963 : Nat.Prime 23754127963 := by
  apply lucas_primality 23754127963 (2 : ZMod 23754127963)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12569, 1), (314983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12569, 1), (314983, 1)] : List FactorBlock).map factorBlockValue).prod) = 23754127963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_12569
      · exact prime_oneHundredTwentyNineDW_314983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23754127963) ^ 11877063981 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23754127963) ^ 7918042654 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23754127963) ^ 1889898 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 23754127963) ^ 75414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_25787995747 : Nat.Prime 25787995747 := by
  apply lucas_primality 25787995747 (3 : ZMod 25787995747)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (37, 1), (41, 2), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (37, 1), (41, 2), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) = 25787995747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_3637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 25787995747) ^ 12893997873 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 25787995747) ^ 8595998582 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 25787995747) ^ 1357262934 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 25787995747) ^ 696972858 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 25787995747) ^ 628975506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 25787995747) ^ 7090458 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_28794848297 : Nat.Prime 28794848297 := by
  apply lucas_primality 28794848297 (3 : ZMod 28794848297)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3599356037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3599356037, 1)] : List FactorBlock).map factorBlockValue).prod) = 28794848297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3599356037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 28794848297) ^ 14397424148 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 28794848297) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_29936099239 : Nat.Prime 29936099239 := by
  apply lucas_primality 29936099239 (3 : ZMod 29936099239)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1531, 1), (191699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1531, 1), (191699, 1)] : List FactorBlock).map factorBlockValue).prod) = 29936099239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_1531
      · exact prime_oneHundredTwentyNineDW_191699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29936099239) ^ 14968049619 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 29936099239) ^ 9978699746 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 29936099239) ^ 1760947014 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 29936099239) ^ 19553298 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 29936099239) ^ 156162 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_36485433097 : Nat.Prime 36485433097 := by
  apply lucas_primality 36485433097 (5 : ZMod 36485433097)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (109, 1), (1992433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (109, 1), (1992433, 1)] : List FactorBlock).map factorBlockValue).prod) = 36485433097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_109
      · exact prime_oneHundredTwentyNineDW_1992433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36485433097) ^ 18242716548 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 36485433097) ^ 12161811032 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 36485433097) ^ 5212204728 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 36485433097) ^ 334728744 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 36485433097) ^ 18312 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_45509803243 : Nat.Prime 45509803243 := by
  apply lucas_primality 45509803243 (2 : ZMod 45509803243)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (161382281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (161382281, 1)] : List FactorBlock).map factorBlockValue).prod) = 45509803243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_161382281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45509803243) ^ 22754901621 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45509803243) ^ 15169934414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45509803243) ^ 968293686 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45509803243) ^ 282 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_47164952837 : Nat.Prime 47164952837 := by
  apply lucas_primality 47164952837 (2 : ZMod 47164952837)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (12659, 1), (32119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (12659, 1), (32119, 1)] : List FactorBlock).map factorBlockValue).prod) = 47164952837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_12659
      · exact prime_oneHundredTwentyNineDW_32119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 47164952837) ^ 23582476418 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 47164952837) ^ 1626377684 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 47164952837) ^ 3725804 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 47164952837) ^ 1468444 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_53194596781 : Nat.Prime 53194596781 := by
  apply lucas_primality 53194596781 (2 : ZMod 53194596781)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (373, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (19, 1), (373, 1), (9623, 1)] : List FactorBlock).map factorBlockValue).prod) = 53194596781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_373
      · exact prime_oneHundredTwentyNineDW_9623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 53194596781) ^ 26597298390 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 17731532260 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 10638919356 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 4091892060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 2799715620 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 142612860 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 53194596781) ^ 5527860 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_56480069099 : Nat.Prime 56480069099 := by
  apply lucas_primality 56480069099 (2 : ZMod 56480069099)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 2), (20628221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 2), (20628221, 1)] : List FactorBlock).map factorBlockValue).prod) = 56480069099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_20628221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 56480069099) ^ 28240034549 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56480069099) ^ 1526488354 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 56480069099) ^ 2738 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_61570712023 : Nat.Prime 61570712023 := by
  apply lucas_primality 61570712023 (3 : ZMod 61570712023)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (853, 1), (12030229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (853, 1), (12030229, 1)] : List FactorBlock).map factorBlockValue).prod) = 61570712023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_853
      · exact prime_oneHundredTwentyNineDW_12030229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 61570712023) ^ 30785356011 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61570712023) ^ 20523570674 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61570712023) ^ 72181374 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61570712023) ^ 5118 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_64910942633 : Nat.Prime 64910942633 := by
  apply lucas_primality 64910942633 (3 : ZMod 64910942633)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (20297, 1), (399757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (20297, 1), (399757, 1)] : List FactorBlock).map factorBlockValue).prod) = 64910942633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_20297
      · exact prime_oneHundredTwentyNineDW_399757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 64910942633) ^ 32455471316 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64910942633) ^ 3198056 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 64910942633) ^ 162376 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_73766928289 : Nat.Prime 73766928289 := by
  apply lucas_primality 73766928289 (7 : ZMod 73766928289)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (768405503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (768405503, 1)] : List FactorBlock).map factorBlockValue).prod) = 73766928289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_768405503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 73766928289) ^ 36883464144 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73766928289) ^ 24588976096 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 73766928289) ^ 96 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_87653870483 : Nat.Prime 87653870483 := by
  apply lucas_primality 87653870483 (2 : ZMod 87653870483)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (1511273629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (1511273629, 1)] : List FactorBlock).map factorBlockValue).prod) = 87653870483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_1511273629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 87653870483) ^ 43826935241 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 87653870483) ^ 3022547258 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 87653870483) ^ 58 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_96156092551 : Nat.Prime 96156092551 := by
  apply lucas_primality 96156092551 (7 : ZMod 96156092551)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (41, 1), (139, 1), (16069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (41, 1), (139, 1), (16069, 1)] : List FactorBlock).map factorBlockValue).prod) = 96156092551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_139
      · exact prime_oneHundredTwentyNineDW_16069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 96156092551) ^ 48078046275 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 32052030850 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 19231218510 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 13736584650 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 2345270550 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 691770450 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 96156092551) ^ 5983950 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_101762258239 : Nat.Prime 101762258239 := by
  apply lucas_primality 101762258239 (3 : ZMod 101762258239)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1013, 1), (5580907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1013, 1), (5580907, 1)] : List FactorBlock).map factorBlockValue).prod) = 101762258239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_1013
      · exact prime_oneHundredTwentyNineDW_5580907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101762258239) ^ 50881129119 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101762258239) ^ 33920752746 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101762258239) ^ 100456326 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 101762258239) ^ 18234 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_101968385747 : Nat.Prime 101968385747 := by
  apply lucas_primality 101968385747 (2 : ZMod 101968385747)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (73, 1), (1325263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (73, 1), (1325263, 1)] : List FactorBlock).map factorBlockValue).prod) = 101968385747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_73
      · exact prime_oneHundredTwentyNineDW_1325263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 101968385747) ^ 50984192873 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101968385747) ^ 5998140338 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101968385747) ^ 3289302766 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101968385747) ^ 1396827202 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 101968385747) ^ 76942 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_102419441381 : Nat.Prime 102419441381 := by
  apply lucas_primality 102419441381 (2 : ZMod 102419441381)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1447, 1), (3539027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1447, 1), (3539027, 1)] : List FactorBlock).map factorBlockValue).prod) = 102419441381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_1447
      · exact prime_oneHundredTwentyNineDW_3539027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102419441381) ^ 51209720690 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102419441381) ^ 20483888276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102419441381) ^ 70780540 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 102419441381) ^ 28940 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_122188924523 : Nat.Prime 122188924523 := by
  apply lucas_primality 122188924523 (2 : ZMod 122188924523)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (8727780323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (8727780323, 1)] : List FactorBlock).map factorBlockValue).prod) = 122188924523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_8727780323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 122188924523) ^ 61094462261 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122188924523) ^ 17455560646 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122188924523) ^ 14 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_122903422531 : Nat.Prime 122903422531 := by
  apply lucas_primality 122903422531 (2 : ZMod 122903422531)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (631, 1), (54559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (631, 1), (54559, 1)] : List FactorBlock).map factorBlockValue).prod) = 122903422531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_631
      · exact prime_oneHundredTwentyNineDW_54559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122903422531) ^ 61451711265 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 40967807510 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 24580684506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 17557631790 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 7229613090 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 194775630 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 122903422531) ^ 2252670 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_124452507577 : Nat.Prime 124452507577 := by
  apply lucas_primality 124452507577 (5 : ZMod 124452507577)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5185521149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5185521149, 1)] : List FactorBlock).map factorBlockValue).prod) = 124452507577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5185521149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 124452507577) ^ 62226253788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 124452507577) ^ 41484169192 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 124452507577) ^ 24 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_126366578209 : Nat.Prime 126366578209 := by
  apply lucas_primality 126366578209 (29 : ZMod 126366578209)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (13, 2), (131, 1), (19819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (13, 2), (131, 1), (19819, 1)] : List FactorBlock).map factorBlockValue).prod) = 126366578209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_131
      · exact prime_oneHundredTwentyNineDW_19819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 126366578209) ^ 63183289104 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 126366578209) ^ 42122192736 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 126366578209) ^ 9720506016 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 126366578209) ^ 964630368 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 126366578209) ^ 6376032 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_139003837673 : Nat.Prime 139003837673 := by
  apply lucas_primality 139003837673 (3 : ZMod 139003837673)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (5107, 1), (486041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (5107, 1), (486041, 1)] : List FactorBlock).map factorBlockValue).prod) = 139003837673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_5107
      · exact prime_oneHundredTwentyNineDW_486041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 139003837673) ^ 69501918836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 139003837673) ^ 19857691096 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 139003837673) ^ 27218296 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 139003837673) ^ 285992 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_181769781169 : Nat.Prime 181769781169 := by
  apply lucas_primality 181769781169 (13 : ZMod 181769781169)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (31, 1), (40719037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (31, 1), (40719037, 1)] : List FactorBlock).map factorBlockValue).prod) = 181769781169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_40719037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 181769781169) ^ 90884890584 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 181769781169) ^ 60589927056 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 181769781169) ^ 5863541328 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 181769781169) ^ 4464 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_186904922573 : Nat.Prime 186904922573 := by
  apply lucas_primality 186904922573 (2 : ZMod 186904922573)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (6823, 1), (360439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (6823, 1), (360439, 1)] : List FactorBlock).map factorBlockValue).prod) = 186904922573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_6823
      · exact prime_oneHundredTwentyNineDW_360439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 186904922573) ^ 93452461286 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 186904922573) ^ 9837101188 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 186904922573) ^ 27393364 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 186904922573) ^ 518548 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_223483179889 : Nat.Prime 223483179889 := by
  apply lucas_primality 223483179889 (11 : ZMod 223483179889)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (661, 1), (2347907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (661, 1), (2347907, 1)] : List FactorBlock).map factorBlockValue).prod) = 223483179889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_661
      · exact prime_oneHundredTwentyNineDW_2347907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 223483179889) ^ 111741589944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 223483179889) ^ 74494393296 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 223483179889) ^ 338098608 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 223483179889) ^ 95184 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_232292135107 : Nat.Prime 232292135107 := by
  apply lucas_primality 232292135107 (2 : ZMod 232292135107)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (523, 1), (1619, 1), (15241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (523, 1), (1619, 1), (15241, 1)] : List FactorBlock).map factorBlockValue).prod) = 232292135107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_523
      · exact prime_oneHundredTwentyNineDW_1619
      · exact prime_oneHundredTwentyNineDW_15241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 232292135107) ^ 116146067553 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 232292135107) ^ 77430711702 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 232292135107) ^ 444153222 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 232292135107) ^ 143478774 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 232292135107) ^ 15241266 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_251473404181 : Nat.Prime 251473404181 := by
  apply lucas_primality 251473404181 (10 : ZMod 251473404181)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (359, 1), (11674717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (359, 1), (11674717, 1)] : List FactorBlock).map factorBlockValue).prod) = 251473404181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_359
      · exact prime_oneHundredTwentyNineDW_11674717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 251473404181) ^ 125736702090 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 251473404181) ^ 83824468060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 251473404181) ^ 50294680836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 251473404181) ^ 700483020 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 251473404181) ^ 21540 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_327202202699 : Nat.Prime 327202202699 := by
  apply lucas_primality 327202202699 (7 : ZMod 327202202699)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (23, 1), (53, 1), (1127809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (23, 1), (53, 1), (1127809, 1)] : List FactorBlock).map factorBlockValue).prod) = 327202202699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_1127809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 327202202699) ^ 163601101349 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 327202202699) ^ 46743171814 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 327202202699) ^ 19247188394 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 327202202699) ^ 14226182726 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 327202202699) ^ 6173626466 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 327202202699) ^ 290122 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_347191274657 : Nat.Prime 347191274657 := by
  apply lucas_primality 347191274657 (3 : ZMod 347191274657)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3923, 1), (2765671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3923, 1), (2765671, 1)] : List FactorBlock).map factorBlockValue).prod) = 347191274657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3923
      · exact prime_oneHundredTwentyNineDW_2765671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 347191274657) ^ 173595637328 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 347191274657) ^ 88501472 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 347191274657) ^ 125536 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_459542833973 : Nat.Prime 459542833973 := by
  apply lucas_primality 459542833973 (2 : ZMod 459542833973)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (661, 1), (3343, 1), (51991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (661, 1), (3343, 1), (51991, 1)] : List FactorBlock).map factorBlockValue).prod) = 459542833973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_661
      · exact prime_oneHundredTwentyNineDW_3343
      · exact prime_oneHundredTwentyNineDW_51991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 459542833973) ^ 229771416986 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 459542833973) ^ 695223652 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 459542833973) ^ 137464204 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 459542833973) ^ 8838892 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_462414295729 : Nat.Prime 462414295729 := by
  apply lucas_primality 462414295729 (37 : ZMod 462414295729)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (7, 1), (11, 1), (19, 1), (139, 1), (15791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (7, 1), (11, 1), (19, 1), (139, 1), (15791, 1)] : List FactorBlock).map factorBlockValue).prod) = 462414295729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_139
      · exact prime_oneHundredTwentyNineDW_15791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 462414295729) ^ 231207147864 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 154138098576 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 66059185104 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 42037663248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 24337594512 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 3326721552 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (37 : ZMod 462414295729) ^ 29283408 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_503706268267 : Nat.Prime 503706268267 := by
  apply lucas_primality 503706268267 (2 : ZMod 503706268267)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (6079, 1), (321163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (6079, 1), (321163, 1)] : List FactorBlock).map factorBlockValue).prod) = 503706268267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_43
      · exact prime_oneHundredTwentyNineDW_6079
      · exact prime_oneHundredTwentyNineDW_321163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 503706268267) ^ 251853134133 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 503706268267) ^ 167902089422 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 503706268267) ^ 11714099262 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 503706268267) ^ 82860054 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 503706268267) ^ 1568382 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_525923222899 : Nat.Prime 525923222899 := by
  apply lucas_primality 525923222899 (7 : ZMod 525923222899)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (87653870483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (87653870483, 1)] : List FactorBlock).map factorBlockValue).prod) = 525923222899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_87653870483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 525923222899) ^ 262961611449 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 525923222899) ^ 175307740966 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 525923222899) ^ 6 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_569643685747 : Nat.Prime 569643685747 := by
  apply lucas_primality 569643685747 (2 : ZMod 569643685747)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (3062600461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (3062600461, 1)] : List FactorBlock).map factorBlockValue).prod) = 569643685747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_3062600461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 569643685747) ^ 284821842873 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 569643685747) ^ 189881228582 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 569643685747) ^ 18375602766 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 569643685747) ^ 186 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_593431567061 : Nat.Prime 593431567061 := by
  apply lucas_primality 593431567061 (2 : ZMod 593431567061)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (53, 1), (197, 1), (69313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (53, 1), (197, 1), (69313, 1)] : List FactorBlock).map factorBlockValue).prod) = 593431567061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_197
      · exact prime_oneHundredTwentyNineDW_69313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 593431567061) ^ 296715783530 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 593431567061) ^ 118686313412 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 593431567061) ^ 14473940660 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 593431567061) ^ 11196822020 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 593431567061) ^ 3012342980 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 593431567061) ^ 8561620 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_614516648287 : Nat.Prime 614516648287 := by
  apply lucas_primality 614516648287 (5 : ZMod 614516648287)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (102419441381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (102419441381, 1)] : List FactorBlock).map factorBlockValue).prod) = 614516648287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_102419441381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 614516648287) ^ 307258324143 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 614516648287) ^ 204838882762 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 614516648287) ^ 6 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_706578100511 : Nat.Prime 706578100511 := by
  apply lucas_primality 706578100511 (29 : ZMod 706578100511)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (179, 1), (2953, 1), (133673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (179, 1), (2953, 1), (133673, 1)] : List FactorBlock).map factorBlockValue).prod) = 706578100511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_179
      · exact prime_oneHundredTwentyNineDW_2953
      · exact prime_oneHundredTwentyNineDW_133673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 706578100511) ^ 353289050255 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 706578100511) ^ 141315620102 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 706578100511) ^ 3947363690 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 706578100511) ^ 239274670 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 706578100511) ^ 5285870 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_930646615543 : Nat.Prime 930646615543 := by
  apply lucas_primality 930646615543 (3 : ZMod 930646615543)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (1166223829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (1166223829, 1)] : List FactorBlock).map factorBlockValue).prod) = 930646615543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_1166223829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 930646615543) ^ 465323307771 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 930646615543) ^ 310215538514 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 930646615543) ^ 132949516506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 930646615543) ^ 48981400818 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 930646615543) ^ 798 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_974979031919 : Nat.Prime 974979031919 := by
  apply lucas_primality 974979031919 (7 : ZMod 974979031919)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (379, 1), (7589, 1), (169489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (379, 1), (7589, 1), (169489, 1)] : List FactorBlock).map factorBlockValue).prod) = 974979031919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_379
      · exact prime_oneHundredTwentyNineDW_7589
      · exact prime_oneHundredTwentyNineDW_169489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 974979031919) ^ 487489515959 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 974979031919) ^ 2572504042 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 974979031919) ^ 128472662 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 974979031919) ^ 5752462 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1061273754263 : Nat.Prime 1061273754263 := by
  apply lucas_primality 1061273754263 (5 : ZMod 1061273754263)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (260417, 1), (2037643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (260417, 1), (2037643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1061273754263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_260417
      · exact prime_oneHundredTwentyNineDW_2037643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1061273754263) ^ 530636877131 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1061273754263) ^ 4075286 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 1061273754263) ^ 520834 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1254313939633 : Nat.Prime 1254313939633 := by
  apply lucas_primality 1254313939633 (7 : ZMod 1254313939633)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (151, 1), (13312043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (151, 1), (13312043, 1)] : List FactorBlock).map factorBlockValue).prod) = 1254313939633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_151
      · exact prime_oneHundredTwentyNineDW_13312043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1254313939633) ^ 627156969816 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1254313939633) ^ 418104646544 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1254313939633) ^ 96485687664 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1254313939633) ^ 8306714832 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 1254313939633) ^ 94224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1274520759529 : Nat.Prime 1274520759529 := by
  apply lucas_primality 1274520759529 (22 : ZMod 1274520759529)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (31, 1), (373, 1), (270157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (31, 1), (373, 1), (270157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1274520759529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_373
      · exact prime_oneHundredTwentyNineDW_270157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 1274520759529) ^ 637260379764 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (22 : ZMod 1274520759529) ^ 424840253176 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (22 : ZMod 1274520759529) ^ 74971809384 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (22 : ZMod 1274520759529) ^ 41113572888 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (22 : ZMod 1274520759529) ^ 3416945736 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (22 : ZMod 1274520759529) ^ 4717704 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1369614255683 : Nat.Prime 1369614255683 := by
  apply lucas_primality 1369614255683 (2 : ZMod 1369614255683)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (22090552511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (22090552511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1369614255683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_22090552511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1369614255683) ^ 684807127841 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1369614255683) ^ 44181105022 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1369614255683) ^ 62 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1580628104239 : Nat.Prime 1580628104239 := by
  apply lucas_primality 1580628104239 (3 : ZMod 1580628104239)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (36677, 1), (7182649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (36677, 1), (7182649, 1)] : List FactorBlock).map factorBlockValue).prod) = 1580628104239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_36677
      · exact prime_oneHundredTwentyNineDW_7182649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1580628104239) ^ 790314052119 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580628104239) ^ 526876034746 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580628104239) ^ 43095894 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580628104239) ^ 220062 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1621314912071 : Nat.Prime 1621314912071 := by
  apply lucas_primality 1621314912071 (29 : ZMod 1621314912071)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (1163, 1), (2845061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (1163, 1), (2845061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1621314912071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_1163
      · exact prime_oneHundredTwentyNineDW_2845061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 1621314912071) ^ 810657456035 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 1621314912071) ^ 324262982414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 1621314912071) ^ 231616416010 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 1621314912071) ^ 1394079890 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 1621314912071) ^ 569870 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1943719994347 : Nat.Prime 1943719994347 := by
  apply lucas_primality 1943719994347 (2 : ZMod 1943719994347)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (163, 1), (8046331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (163, 1), (8046331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1943719994347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_163
      · exact prime_oneHundredTwentyNineDW_8046331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1943719994347) ^ 971859997173 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1943719994347) ^ 647906664782 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1943719994347) ^ 149516922642 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1943719994347) ^ 102301052334 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1943719994347) ^ 11924662542 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1943719994347) ^ 241566 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2075257924829 : Nat.Prime 2075257924829 := by
  apply lucas_primality 2075257924829 (2 : ZMod 2075257924829)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (47164952837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (47164952837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2075257924829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_47164952837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2075257924829) ^ 1037628962414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075257924829) ^ 188659811348 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2075257924829) ^ 44 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3528819336877 : Nat.Prime 3528819336877 := by
  apply lucas_primality 3528819336877 (5 : ZMod 3528819336877)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (207401, 1), (1417873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (207401, 1), (1417873, 1)] : List FactorBlock).map factorBlockValue).prod) = 3528819336877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_207401
      · exact prime_oneHundredTwentyNineDW_1417873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3528819336877) ^ 1764409668438 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3528819336877) ^ 1176273112292 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3528819336877) ^ 17014476 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3528819336877) ^ 2488812 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3738516404141 : Nat.Prime 3738516404141 := by
  apply lucas_primality 3738516404141 (10 : ZMod 3738516404141)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (52903, 1), (504767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (52903, 1), (504767, 1)] : List FactorBlock).map factorBlockValue).prod) = 3738516404141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_52903
      · exact prime_oneHundredTwentyNineDW_504767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3738516404141) ^ 1869258202070 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 3738516404141) ^ 747703280828 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 3738516404141) ^ 534073772020 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 3738516404141) ^ 70667380 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 3738516404141) ^ 7406420 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3840644698733 : Nat.Prime 3840644698733 := by
  apply lucas_primality 3840644698733 (2 : ZMod 3840644698733)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (56480069099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (56480069099, 1)] : List FactorBlock).map factorBlockValue).prod) = 3840644698733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_56480069099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3840644698733) ^ 1920322349366 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3840644698733) ^ 225920276396 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3840644698733) ^ 68 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4511316316063 : Nat.Prime 4511316316063 := by
  apply lucas_primality 4511316316063 (5 : ZMod 4511316316063)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (859, 1), (875303903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (859, 1), (875303903, 1)] : List FactorBlock).map factorBlockValue).prod) = 4511316316063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_859
      · exact prime_oneHundredTwentyNineDW_875303903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4511316316063) ^ 2255658158031 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4511316316063) ^ 1503772105354 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4511316316063) ^ 5251823418 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4511316316063) ^ 5154 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4952117804903 : Nat.Prime 4952117804903 := by
  apply lucas_primality 4952117804903 (5 : ZMod 4952117804903)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (5023, 1), (15901427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (5023, 1), (15901427, 1)] : List FactorBlock).map factorBlockValue).prod) = 4952117804903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_5023
      · exact prime_oneHundredTwentyNineDW_15901427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4952117804903) ^ 2476058902451 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4952117804903) ^ 159745735642 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4952117804903) ^ 985888474 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 4952117804903) ^ 311426 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5910788354209 : Nat.Prime 5910788354209 := by
  apply lucas_primality 5910788354209 (11 : ZMod 5910788354209)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (61570712023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (61570712023, 1)] : List FactorBlock).map factorBlockValue).prod) = 5910788354209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_61570712023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 5910788354209) ^ 2955394177104 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 5910788354209) ^ 1970262784736 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 5910788354209) ^ 96 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_7586302193629 : Nat.Prime 7586302193629 := by
  apply lucas_primality 7586302193629 (2 : ZMod 7586302193629)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (181, 1), (877, 1), (907, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (181, 1), (877, 1), (907, 1), (4391, 1)] : List FactorBlock).map factorBlockValue).prod) = 7586302193629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_181
      · exact prime_oneHundredTwentyNineDW_877
      · exact prime_oneHundredTwentyNineDW_907
      · exact prime_oneHundredTwentyNineDW_4391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7586302193629) ^ 3793151096814 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586302193629) ^ 2528767397876 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586302193629) ^ 41913271788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586302193629) ^ 8650287564 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586302193629) ^ 8364170004 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 7586302193629) ^ 1727693508 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_11167759386517 : Nat.Prime 11167759386517 := by
  apply lucas_primality 11167759386517 (2 : ZMod 11167759386517)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (930646615543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (930646615543, 1)] : List FactorBlock).map factorBlockValue).prod) = 11167759386517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_930646615543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11167759386517) ^ 5583879693258 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11167759386517) ^ 3722586462172 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 11167759386517) ^ 12 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_12463270301347 : Nat.Prime 12463270301347 := by
  apply lucas_primality 12463270301347 (2 : ZMod 12463270301347)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (122188924523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (122188924523, 1)] : List FactorBlock).map factorBlockValue).prod) = 12463270301347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_122188924523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12463270301347) ^ 6231635150673 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12463270301347) ^ 4154423433782 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12463270301347) ^ 733133547138 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12463270301347) ^ 102 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_13965858679081 : Nat.Prime 13965858679081 := by
  apply lucas_primality 13965858679081 (29 : ZMod 13965858679081)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (5021, 1), (301027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (11, 1), (5021, 1), (301027, 1)] : List FactorBlock).map factorBlockValue).prod) = 13965858679081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_5021
      · exact prime_oneHundredTwentyNineDW_301027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 13965858679081) ^ 6982929339540 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 4655286226360 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 2793171735816 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 1995122668440 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 1269623516280 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 2781489480 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (29 : ZMod 13965858679081) ^ 46394040 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_14877370948493 : Nat.Prime 14877370948493 := by
  apply lucas_primality 14877370948493 (2 : ZMod 14877370948493)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (37, 1), (20149, 1), (383767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (37, 1), (20149, 1), (383767, 1)] : List FactorBlock).map factorBlockValue).prod) = 14877370948493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_20149
      · exact prime_oneHundredTwentyNineDW_383767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14877370948493) ^ 7438685474246 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14877370948493) ^ 1144413149884 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14877370948493) ^ 402091106716 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14877370948493) ^ 738367708 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14877370948493) ^ 38766676 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_15747023677513 : Nat.Prime 15747023677513 := by
  apply lucas_primality 15747023677513 (13 : ZMod 15747023677513)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (41, 1), (163, 1), (98178361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (41, 1), (163, 1), (98178361, 1)] : List FactorBlock).map factorBlockValue).prod) = 15747023677513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_163
      · exact prime_oneHundredTwentyNineDW_98178361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 15747023677513) ^ 7873511838756 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 15747023677513) ^ 5249007892504 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 15747023677513) ^ 384073748232 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 15747023677513) ^ 96607507224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 15747023677513) ^ 160392 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_18086563013843 : Nat.Prime 18086563013843 := by
  apply lucas_primality 18086563013843 (2 : ZMod 18086563013843)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8389, 1), (1077992789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8389, 1), (1077992789, 1)] : List FactorBlock).map factorBlockValue).prod) = 18086563013843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_8389
      · exact prime_oneHundredTwentyNineDW_1077992789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 18086563013843) ^ 9043281506921 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18086563013843) ^ 2155985578 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 18086563013843) ^ 16778 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_21142211010251 : Nat.Prime 21142211010251 := by
  apply lucas_primality 21142211010251 (2 : ZMod 21142211010251)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (11, 1), (97, 1), (769, 1), (103067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (11, 1), (97, 1), (769, 1), (103067, 1)] : List FactorBlock).map factorBlockValue).prod) = 21142211010251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_97
      · exact prime_oneHundredTwentyNineDW_769
      · exact prime_oneHundredTwentyNineDW_103067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21142211010251) ^ 10571105505125 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21142211010251) ^ 4228442202050 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21142211010251) ^ 1922019182750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21142211010251) ^ 217960938250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21142211010251) ^ 27493122250 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21142211010251) ^ 205130750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_22885150027139 : Nat.Prime 22885150027139 := by
  apply lucas_primality 22885150027139 (2 : ZMod 22885150027139)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (96156092551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (96156092551, 1)] : List FactorBlock).map factorBlockValue).prod) = 22885150027139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_96156092551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22885150027139) ^ 11442575013569 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22885150027139) ^ 3269307146734 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22885150027139) ^ 1346185295714 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22885150027139) ^ 238 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_26340705467663 : Nat.Prime 26340705467663 := by
  apply lucas_primality 26340705467663 (5 : ZMod 26340705467663)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113189, 1), (116357179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113189, 1), (116357179, 1)] : List FactorBlock).map factorBlockValue).prod) = 26340705467663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_113189
      · exact prime_oneHundredTwentyNineDW_116357179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26340705467663) ^ 13170352733831 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 26340705467663) ^ 232714358 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 26340705467663) ^ 226378 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_38916802764131 : Nat.Prime 38916802764131 := by
  apply lucas_primality 38916802764131 (2 : ZMod 38916802764131)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11411, 1), (341046383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11411, 1), (341046383, 1)] : List FactorBlock).map factorBlockValue).prod) = 38916802764131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11411
      · exact prime_oneHundredTwentyNineDW_341046383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 38916802764131) ^ 19458401382065 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 38916802764131) ^ 7783360552826 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 38916802764131) ^ 3410463830 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 38916802764131) ^ 114110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_39890495408917 : Nat.Prime 39890495408917 := by
  apply lucas_primality 39890495408917 (5 : ZMod 39890495408917)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (53, 1), (3571, 1), (924419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (53, 1), (3571, 1), (924419, 1)] : List FactorBlock).map factorBlockValue).prod) = 39890495408917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_3571
      · exact prime_oneHundredTwentyNineDW_924419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 39890495408917) ^ 19945247704458 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 39890495408917) ^ 13296831802972 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 39890495408917) ^ 2099499758364 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 39890495408917) ^ 752650856772 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 39890495408917) ^ 11170679196 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 39890495408917) ^ 43151964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_46587629671529 : Nat.Prime 46587629671529 := by
  apply lucas_primality 46587629671529 (3 : ZMod 46587629671529)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (47, 1), (569, 1), (19796017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (47, 1), (569, 1), (19796017, 1)] : List FactorBlock).map factorBlockValue).prod) = 46587629671529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_569
      · exact prime_oneHundredTwentyNineDW_19796017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46587629671529) ^ 23293814835764 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46587629671529) ^ 4235239061048 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46587629671529) ^ 991226163224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46587629671529) ^ 81876326312 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 46587629671529) ^ 2353384 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_66587658584977 : Nat.Prime 66587658584977 := by
  apply lucas_primality 66587658584977 (7 : ZMod 66587658584977)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (462414295729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (462414295729, 1)] : List FactorBlock).map factorBlockValue).prod) = 66587658584977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_462414295729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 66587658584977) ^ 33293829292488 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 66587658584977) ^ 22195886194992 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 66587658584977) ^ 144 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_68101333843331 : Nat.Prime 68101333843331 := by
  apply lucas_primality 68101333843331 (2 : ZMod 68101333843331)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19861, 1), (342889753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19861, 1), (342889753, 1)] : List FactorBlock).map factorBlockValue).prod) = 68101333843331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_19861
      · exact prime_oneHundredTwentyNineDW_342889753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 68101333843331) ^ 34050666921665 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 68101333843331) ^ 13620266768666 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 68101333843331) ^ 3428897530 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 68101333843331) ^ 198610 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_84209475177251 : Nat.Prime 84209475177251 := by
  apply lucas_primality 84209475177251 (2 : ZMod 84209475177251)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (156319, 1), (2154811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (156319, 1), (2154811, 1)] : List FactorBlock).map factorBlockValue).prod) = 84209475177251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_156319
      · exact prime_oneHundredTwentyNineDW_2154811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84209475177251) ^ 42104737588625 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 84209475177251) ^ 16841895035450 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 84209475177251) ^ 538702750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 84209475177251) ^ 39079750 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_97558475480759 : Nat.Prime 97558475480759 := by
  apply lucas_primality 97558475480759 (13 : ZMod 97558475480759)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (191, 1), (1087, 1), (6349951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (191, 1), (1087, 1), (6349951, 1)] : List FactorBlock).map factorBlockValue).prod) = 97558475480759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_191
      · exact prime_oneHundredTwentyNineDW_1087
      · exact prime_oneHundredTwentyNineDW_6349951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 97558475480759) ^ 48779237740379 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 97558475480759) ^ 2636715553534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 97558475480759) ^ 510777358538 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 97558475480759) ^ 89750207434 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 97558475480759) ^ 15363658 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_99152935398743 : Nat.Prime 99152935398743 := by
  apply lucas_primality 99152935398743 (5 : ZMod 99152935398743)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (757, 1), (42433, 1), (1543391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (757, 1), (42433, 1), (1543391, 1)] : List FactorBlock).map factorBlockValue).prod) = 99152935398743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_757
      · exact prime_oneHundredTwentyNineDW_42433
      · exact prime_oneHundredTwentyNineDW_1543391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 99152935398743) ^ 49576467699371 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 99152935398743) ^ 130981420606 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 99152935398743) ^ 2336693974 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 99152935398743) ^ 64243562 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_123763947127493 : Nat.Prime 123763947127493 := by
  apply lucas_primality 123763947127493 (2 : ZMod 123763947127493)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (190667, 1), (23182517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (190667, 1), (23182517, 1)] : List FactorBlock).map factorBlockValue).prod) = 123763947127493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_190667
      · exact prime_oneHundredTwentyNineDW_23182517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 123763947127493) ^ 61881973563746 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123763947127493) ^ 17680563875356 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123763947127493) ^ 649110476 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 123763947127493) ^ 5338676 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_134504126934553 : Nat.Prime 134504126934553 := by
  apply lucas_primality 134504126934553 (7 : ZMod 134504126934553)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1499, 1), (1246239409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1499, 1), (1246239409, 1)] : List FactorBlock).map factorBlockValue).prod) = 134504126934553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_1499
      · exact prime_oneHundredTwentyNineDW_1246239409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 134504126934553) ^ 67252063467276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 134504126934553) ^ 44834708978184 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 134504126934553) ^ 89729237448 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 134504126934553) ^ 107928 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_151515197991299 : Nat.Prime 151515197991299 := by
  apply lucas_primality 151515197991299 (2 : ZMod 151515197991299)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (449, 1), (2311, 1), (73009591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (449, 1), (2311, 1), (73009591, 1)] : List FactorBlock).map factorBlockValue).prod) = 151515197991299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_449
      · exact prime_oneHundredTwentyNineDW_2311
      · exact prime_oneHundredTwentyNineDW_73009591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 151515197991299) ^ 75757598995649 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 151515197991299) ^ 337450329602 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 151515197991299) ^ 65562612718 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 151515197991299) ^ 2075278 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_158467769756897 : Nat.Prime 158467769756897 := by
  apply lucas_primality 158467769756897 (3 : ZMod 158467769756897)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (4952117804903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (4952117804903, 1)] : List FactorBlock).map factorBlockValue).prod) = 158467769756897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_4952117804903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 158467769756897) ^ 79233884878448 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 158467769756897) ^ 32 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_160836785995243 : Nat.Prime 160836785995243 := by
  apply lucas_primality 160836785995243 (2 : ZMod 160836785995243)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (19753, 1), (27695231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (19753, 1), (27695231, 1)] : List FactorBlock).map factorBlockValue).prod) = 160836785995243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_19753
      · exact prime_oneHundredTwentyNineDW_27695231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 160836785995243) ^ 80418392997621 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 160836785995243) ^ 53612261998414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 160836785995243) ^ 22976683713606 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 160836785995243) ^ 8142397914 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 160836785995243) ^ 5807382 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_223949252448011 : Nat.Prime 223949252448011 := by
  apply lucas_primality 223949252448011 (2 : ZMod 223949252448011)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (421, 1), (53194596781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (421, 1), (53194596781, 1)] : List FactorBlock).map factorBlockValue).prod) = 223949252448011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_421
      · exact prime_oneHundredTwentyNineDW_53194596781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 223949252448011) ^ 111974626224005 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 223949252448011) ^ 44789850489602 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 223949252448011) ^ 531945967810 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 223949252448011) ^ 4210 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_298943093867207 : Nat.Prime 298943093867207 := by
  apply lucas_primality 298943093867207 (5 : ZMod 298943093867207)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (20297, 1), (7364218699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (20297, 1), (7364218699, 1)] : List FactorBlock).map factorBlockValue).prod) = 298943093867207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_20297
      · exact prime_oneHundredTwentyNineDW_7364218699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 298943093867207) ^ 149471546933603 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 298943093867207) ^ 14728437398 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 298943093867207) ^ 40594 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_414196654315427 : Nat.Prime 414196654315427 := by
  apply lucas_primality 414196654315427 (2 : ZMod 414196654315427)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (173, 1), (5179, 1), (13596767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (173, 1), (5179, 1), (13596767, 1)] : List FactorBlock).map factorBlockValue).prod) = 414196654315427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_173
      · exact prime_oneHundredTwentyNineDW_5179
      · exact prime_oneHundredTwentyNineDW_13596767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 414196654315427) ^ 207098327157713 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414196654315427) ^ 24364509077378 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414196654315427) ^ 2394200313962 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414196654315427) ^ 79976183494 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 414196654315427) ^ 30462878 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_457230437639509 : Nat.Prime 457230437639509 := by
  apply lucas_primality 457230437639509 (6 : ZMod 457230437639509)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (73, 1), (151, 1), (433, 1), (26699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (73, 1), (151, 1), (433, 1), (26699, 1)] : List FactorBlock).map factorBlockValue).prod) = 457230437639509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_73
      · exact prime_oneHundredTwentyNineDW_151
      · exact prime_oneHundredTwentyNineDW_433
      · exact prime_oneHundredTwentyNineDW_26699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 457230437639509) ^ 228615218819754 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 152410145879836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 35171572126116 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 19879584245196 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 6263430652596 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 3028016143308 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 1055959440276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 457230437639509) ^ 17125376892 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_526858068789827 : Nat.Prime 526858068789827 := by
  apply lucas_primality 526858068789827 (2 : ZMod 526858068789827)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3889, 1), (4073, 1), (16630729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3889, 1), (4073, 1), (16630729, 1)] : List FactorBlock).map factorBlockValue).prod) = 526858068789827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3889
      · exact prime_oneHundredTwentyNineDW_4073
      · exact prime_oneHundredTwentyNineDW_16630729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 526858068789827) ^ 263429034394913 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 526858068789827) ^ 135473918434 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 526858068789827) ^ 129353810162 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 526858068789827) ^ 31679794 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_527766389051593 : Nat.Prime 527766389051593 := by
  apply lucas_primality 527766389051593 (10 : ZMod 527766389051593)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7103, 1), (3095912461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7103, 1), (3095912461, 1)] : List FactorBlock).map factorBlockValue).prod) = 527766389051593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7103
      · exact prime_oneHundredTwentyNineDW_3095912461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 527766389051593) ^ 263883194525796 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 527766389051593) ^ 175922129683864 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 527766389051593) ^ 74301899064 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 527766389051593) ^ 170472 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_807024761607319 : Nat.Prime 807024761607319 := by
  apply lucas_primality 807024761607319 (3 : ZMod 807024761607319)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (134504126934553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (134504126934553, 1)] : List FactorBlock).map factorBlockValue).prod) = 807024761607319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_134504126934553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 807024761607319) ^ 403512380803659 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 807024761607319) ^ 269008253869106 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 807024761607319) ^ 6 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_910401925157869 : Nat.Prime 910401925157869 := by
  apply lucas_primality 910401925157869 (14 : ZMod 910401925157869)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (13, 1), (126443, 1), (4195861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (13, 1), (126443, 1), (4195861, 1)] : List FactorBlock).map factorBlockValue).prod) = 910401925157869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_126443
      · exact prime_oneHundredTwentyNineDW_4195861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 910401925157869) ^ 455200962578934 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 910401925157869) ^ 303467308385956 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 910401925157869) ^ 82763811377988 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 910401925157869) ^ 70030917319836 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 910401925157869) ^ 7200097476 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 910401925157869) ^ 216976188 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_987134707669897 : Nat.Prime 987134707669897 := by
  apply lucas_primality 987134707669897 (5 : ZMod 987134707669897)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (7993, 1), (23496937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (7993, 1), (23496937, 1)] : List FactorBlock).map factorBlockValue).prod) = 987134707669897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_73
      · exact prime_oneHundredTwentyNineDW_7993
      · exact prime_oneHundredTwentyNineDW_23496937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 987134707669897) ^ 493567353834948 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 987134707669897) ^ 329044902556632 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 987134707669897) ^ 13522393255752 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 987134707669897) ^ 123499900872 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 987134707669897) ^ 42011208 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1006581716363677 : Nat.Prime 1006581716363677 := by
  apply lucas_primality 1006581716363677 (2 : ZMod 1006581716363677)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1439, 1), (18127, 1), (3215741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1439, 1), (18127, 1), (3215741, 1)] : List FactorBlock).map factorBlockValue).prod) = 1006581716363677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_1439
      · exact prime_oneHundredTwentyNineDW_18127
      · exact prime_oneHundredTwentyNineDW_3215741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1006581716363677) ^ 503290858181838 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006581716363677) ^ 335527238787892 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006581716363677) ^ 699500845284 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006581716363677) ^ 55529415588 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1006581716363677) ^ 313017036 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1035612220688047 : Nat.Prime 1035612220688047 := by
  apply lucas_primality 1035612220688047 (6 : ZMod 1035612220688047)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (569643685747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (569643685747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1035612220688047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_101
      · exact prime_oneHundredTwentyNineDW_569643685747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1035612220688047) ^ 517806110344023 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1035612220688047) ^ 345204073562682 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1035612220688047) ^ 10253586343446 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 1035612220688047) ^ 1818 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1204165253268917 : Nat.Prime 1204165253268917 := by
  apply lucas_primality 1204165253268917 (2 : ZMod 1204165253268917)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (4421, 1), (8117, 1), (364739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (4421, 1), (8117, 1), (364739, 1)] : List FactorBlock).map factorBlockValue).prod) = 1204165253268917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_4421
      · exact prime_oneHundredTwentyNineDW_8117
      · exact prime_oneHundredTwentyNineDW_364739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1204165253268917) ^ 602082626634458 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204165253268917) ^ 52355011011692 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204165253268917) ^ 272373954596 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204165253268917) ^ 148351022948 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1204165253268917) ^ 3301443644 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1800848083149217 : Nat.Prime 1800848083149217 := by
  apply lucas_primality 1800848083149217 (13 : ZMod 1800848083149217)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (17, 1), (173, 1), (2126128777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (17, 1), (173, 1), (2126128777, 1)] : List FactorBlock).map factorBlockValue).prod) = 1800848083149217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_173
      · exact prime_oneHundredTwentyNineDW_2126128777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1800848083149217) ^ 900424041574608 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1800848083149217) ^ 600282694383072 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1800848083149217) ^ 105932240185248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1800848083149217) ^ 10409526492192 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 1800848083149217) ^ 847008 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2648658083822039 : Nat.Prime 2648658083822039 := by
  apply lucas_primality 2648658083822039 (11 : ZMod 2648658083822039)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (31, 1), (1663, 1), (9887, 1), (152837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (31, 1), (1663, 1), (9887, 1), (152837, 1)] : List FactorBlock).map factorBlockValue).prod) = 2648658083822039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_1663
      · exact prime_oneHundredTwentyNineDW_9887
      · exact prime_oneHundredTwentyNineDW_152837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2648658083822039) ^ 1324329041911019 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2648658083822039) ^ 155803416695414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2648658083822039) ^ 85440583349098 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2648658083822039) ^ 1592698787626 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2648658083822039) ^ 267892999274 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 2648658083822039) ^ 17329953374 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6046098754867139 : Nat.Prime 6046098754867139 := by
  apply lucas_primality 6046098754867139 (2 : ZMod 6046098754867139)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (10657, 1), (25787995747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (10657, 1), (25787995747, 1)] : List FactorBlock).map factorBlockValue).prod) = 6046098754867139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_10657
      · exact prime_oneHundredTwentyNineDW_25787995747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6046098754867139) ^ 3023049377433569 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6046098754867139) ^ 549645341351558 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6046098754867139) ^ 567335906434 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6046098754867139) ^ 234454 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6202349391556547 : Nat.Prime 6202349391556547 := by
  apply lucas_primality 6202349391556547 (2 : ZMod 6202349391556547)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (337, 1), (877, 1), (10492929077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (337, 1), (877, 1), (10492929077, 1)] : List FactorBlock).map factorBlockValue).prod) = 6202349391556547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_337
      · exact prime_oneHundredTwentyNineDW_877
      · exact prime_oneHundredTwentyNineDW_10492929077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6202349391556547) ^ 3101174695778273 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6202349391556547) ^ 18404597601058 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6202349391556547) ^ 7072234197898 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6202349391556547) ^ 591098 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_8858559508350031 : Nat.Prime 8858559508350031 := by
  apply lucas_primality 8858559508350031 (6 : ZMod 8858559508350031)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (1063, 1), (4025867683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (1063, 1), (4025867683, 1)] : List FactorBlock).map factorBlockValue).prod) = 8858559508350031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_1063
      · exact prime_oneHundredTwentyNineDW_4025867683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8858559508350031) ^ 4429279754175015 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8858559508350031) ^ 2952853169450010 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8858559508350031) ^ 1771711901670006 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8858559508350031) ^ 385154761232610 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8858559508350031) ^ 8333546103810 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 8858559508350031) ^ 2200410 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_9133907841129317 : Nat.Prime 9133907841129317 := by
  apply lucas_primality 9133907841129317 (2 : ZMod 9133907841129317)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (43, 1), (7586302193629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (43, 1), (7586302193629, 1)] : List FactorBlock).map factorBlockValue).prod) = 9133907841129317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_43
      · exact prime_oneHundredTwentyNineDW_7586302193629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9133907841129317) ^ 4566953920564658 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9133907841129317) ^ 1304843977304188 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9133907841129317) ^ 212416461421612 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9133907841129317) ^ 1204 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_12236951005771007 : Nat.Prime 12236951005771007 := by
  apply lucas_primality 12236951005771007 (5 : ZMod 12236951005771007)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1211813, 1), (36323929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1211813, 1), (36323929, 1)] : List FactorBlock).map factorBlockValue).prod) = 12236951005771007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_139
      · exact prime_oneHundredTwentyNineDW_1211813
      · exact prime_oneHundredTwentyNineDW_36323929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12236951005771007) ^ 6118475502885503 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 12236951005771007) ^ 88035618746554 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 12236951005771007) ^ 10098052262 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 12236951005771007) ^ 336884014 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_13478898079334659 : Nat.Prime 13478898079334659 := by
  apply lucas_primality 13478898079334659 (10 : ZMod 13478898079334659)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (151, 1), (14877370948493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (151, 1), (14877370948493, 1)] : List FactorBlock).map factorBlockValue).prod) = 13478898079334659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_151
      · exact prime_oneHundredTwentyNineDW_14877370948493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 13478898079334659) ^ 6739449039667329 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 13478898079334659) ^ 4492966026444886 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 13478898079334659) ^ 89264225690958 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 13478898079334659) ^ 906 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_14276662363473347 : Nat.Prime 14276662363473347 := by
  apply lucas_primality 14276662363473347 (2 : ZMod 14276662363473347)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (271, 1), (26340705467663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (271, 1), (26340705467663, 1)] : List FactorBlock).map factorBlockValue).prod) = 14276662363473347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_271
      · exact prime_oneHundredTwentyNineDW_26340705467663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14276662363473347) ^ 7138331181736673 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14276662363473347) ^ 52681410935326 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14276662363473347) ^ 542 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_14709182357355053 : Nat.Prime 14709182357355053 := by
  apply lucas_primality 14709182357355053 (2 : ZMod 14709182357355053)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2089, 1), (251473404181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2089, 1), (251473404181, 1)] : List FactorBlock).map factorBlockValue).prod) = 14709182357355053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_2089
      · exact prime_oneHundredTwentyNineDW_251473404181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14709182357355053) ^ 7354591178677526 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709182357355053) ^ 2101311765336436 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709182357355053) ^ 7041255317068 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 14709182357355053) ^ 58492 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_22642875238254917 : Nat.Prime 22642875238254917 := by
  apply lucas_primality 22642875238254917 (2 : ZMod 22642875238254917)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4513, 1), (1254313939633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4513, 1), (1254313939633, 1)] : List FactorBlock).map factorBlockValue).prod) = 22642875238254917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_4513
      · exact prime_oneHundredTwentyNineDW_1254313939633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22642875238254917) ^ 11321437619127458 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22642875238254917) ^ 5017255758532 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 22642875238254917) ^ 18052 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_32323856939990219 : Nat.Prime 32323856939990219 := by
  apply lucas_primality 32323856939990219 (2 : ZMod 32323856939990219)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163, 1), (99152935398743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163, 1), (99152935398743, 1)] : List FactorBlock).map factorBlockValue).prod) = 32323856939990219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_163
      · exact prime_oneHundredTwentyNineDW_99152935398743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32323856939990219) ^ 16161928469995109 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 32323856939990219) ^ 198305870797486 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 32323856939990219) ^ 326 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_33782905230676879 : Nat.Prime 33782905230676879 := by
  apply lucas_primality 33782905230676879 (6 : ZMod 33782905230676879)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4111, 1), (1369614255683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4111, 1), (1369614255683, 1)] : List FactorBlock).map factorBlockValue).prod) = 33782905230676879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_4111
      · exact prime_oneHundredTwentyNineDW_1369614255683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 33782905230676879) ^ 16891452615338439 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33782905230676879) ^ 11260968410225626 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33782905230676879) ^ 8217685534098 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 33782905230676879) ^ 24666 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_36634128349737929 : Nat.Prime 36634128349737929 := by
  apply lucas_primality 36634128349737929 (3 : ZMod 36634128349737929)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (37, 1), (123763947127493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (37, 1), (123763947127493, 1)] : List FactorBlock).map factorBlockValue).prod) = 36634128349737929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_123763947127493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36634128349737929) ^ 18317064174868964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36634128349737929) ^ 990111577019944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36634128349737929) ^ 296 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_37403892117184123 : Nat.Prime 37403892117184123 := by
  apply lucas_primality 37403892117184123 (5 : ZMod 37403892117184123)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (3557, 1), (64910942633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (3557, 1), (64910942633, 1)] : List FactorBlock).map factorBlockValue).prod) = 37403892117184123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_3557
      · exact prime_oneHundredTwentyNineDW_64910942633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37403892117184123) ^ 18701946058592061 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 37403892117184123) ^ 12467964039061374 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 37403892117184123) ^ 10515572706546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 37403892117184123) ^ 576234 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_61149120872515409 : Nat.Prime 61149120872515409 := by
  apply lucas_primality 61149120872515409 (3 : ZMod 61149120872515409)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (167, 1), (22885150027139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (167, 1), (22885150027139, 1)] : List FactorBlock).map factorBlockValue).prod) = 61149120872515409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_167
      · exact prime_oneHundredTwentyNineDW_22885150027139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 61149120872515409) ^ 30574560436257704 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61149120872515409) ^ 366162400434224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 61149120872515409) ^ 2672 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_68320923166906301 : Nat.Prime 68320923166906301 := by
  apply lucas_primality 68320923166906301 (3 : ZMod 68320923166906301)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (53, 1), (2749, 1), (426295189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (53, 1), (2749, 1), (426295189, 1)] : List FactorBlock).map factorBlockValue).prod) = 68320923166906301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_2749
      · exact prime_oneHundredTwentyNineDW_426295189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68320923166906301) ^ 34160461583453150 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68320923166906301) ^ 13664184633381260 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68320923166906301) ^ 6210993015173300 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68320923166906301) ^ 1289074022017100 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68320923166906301) ^ 24853009518700 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68320923166906301) ^ 160266700 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_119662568780460793 : Nat.Prime 119662568780460793 := by
  apply lucas_primality 119662568780460793 (5 : ZMod 119662568780460793)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (160836785995243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (160836785995243, 1)] : List FactorBlock).map factorBlockValue).prod) = 119662568780460793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_160836785995243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119662568780460793) ^ 59831284390230396 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 119662568780460793) ^ 39887522926820264 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 119662568780460793) ^ 3860082863885832 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 119662568780460793) ^ 744 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_207195544996051921 : Nat.Prime 207195544996051921 := by
  apply lucas_primality 207195544996051921 (19 : ZMod 207195544996051921)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (127301, 1), (88073779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (11, 1), (127301, 1), (88073779, 1)] : List FactorBlock).map factorBlockValue).prod) = 207195544996051921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_127301
      · exact prime_oneHundredTwentyNineDW_88073779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 207195544996051921) ^ 103597772498025960 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 69065181665350640 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 41439108999210384 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 29599363570864560 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 18835958636004720 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 1627603435920 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (19 : ZMod 207195544996051921) ^ 2352522480 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_215764781356123229 : Nat.Prime 215764781356123229 := by
  apply lucas_primality 215764781356123229 (2 : ZMod 215764781356123229)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1201, 1), (1231, 1), (36485433097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1201, 1), (1231, 1), (36485433097, 1)] : List FactorBlock).map factorBlockValue).prod) = 215764781356123229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_1201
      · exact prime_oneHundredTwentyNineDW_1231
      · exact prime_oneHundredTwentyNineDW_36485433097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 215764781356123229) ^ 107882390678061614 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 215764781356123229) ^ 179654272569628 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 215764781356123229) ^ 175276020597988 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 215764781356123229) ^ 5913724 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_252603878142790571 : Nat.Prime 252603878142790571 := by
  apply lucas_primality 252603878142790571 (10 : ZMod 252603878142790571)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (601, 1), (62563, 1), (61073849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (601, 1), (62563, 1), (61073849, 1)] : List FactorBlock).map factorBlockValue).prod) = 252603878142790571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_601
      · exact prime_oneHundredTwentyNineDW_62563
      · exact prime_oneHundredTwentyNineDW_61073849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 252603878142790571) ^ 126301939071395285 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 252603878142790571) ^ 50520775628558114 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 252603878142790571) ^ 22963988922071870 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 252603878142790571) ^ 420305953648570 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 252603878142790571) ^ 4037592157390 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (10 : ZMod 252603878142790571) ^ 4136039930 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_302780484693952039 : Nat.Prime 302780484693952039 := by
  apply lucas_primality 302780484693952039 (11 : ZMod 302780484693952039)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (101, 1), (509, 1), (327202202699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (101, 1), (509, 1), (327202202699, 1)] : List FactorBlock).map factorBlockValue).prod) = 302780484693952039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_101
      · exact prime_oneHundredTwentyNineDW_509
      · exact prime_oneHundredTwentyNineDW_327202202699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 302780484693952039) ^ 151390242346976019 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 302780484693952039) ^ 100926828231317346 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 302780484693952039) ^ 2997826581128238 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 302780484693952039) ^ 594853604506782 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 302780484693952039) ^ 925362 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_337236613575790601 : Nat.Prime 337236613575790601 := by
  apply lucas_primality 337236613575790601 (3 : ZMod 337236613575790601)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (7, 1), (19, 1), (251, 1), (397, 1), (7901, 1), (16103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (7, 1), (19, 1), (251, 1), (397, 1), (7901, 1), (16103, 1)] : List FactorBlock).map factorBlockValue).prod) = 337236613575790601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_251
      · exact prime_oneHundredTwentyNineDW_397
      · exact prime_oneHundredTwentyNineDW_7901
      · exact prime_oneHundredTwentyNineDW_16103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 337236613575790601) ^ 168618306787895300 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 67447322715158120 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 48176659082255800 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 17749295451357400 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 1343572165640600 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 849462502709800 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 42682776050600 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 337236613575790601) ^ 20942471190200 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_532773603223871939 : Nat.Prime 532773603223871939 := by
  apply lucas_primality 532773603223871939 (2 : ZMod 532773603223871939)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1425253, 1), (186904922573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1425253, 1), (186904922573, 1)] : List FactorBlock).map factorBlockValue).prod) = 532773603223871939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_1425253
      · exact prime_oneHundredTwentyNineDW_186904922573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 532773603223871939) ^ 266386801611935969 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 532773603223871939) ^ 373809845146 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 532773603223871939) ^ 2850506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_915464440000220221 : Nat.Prime 915464440000220221 := by
  apply lucas_primality 915464440000220221 (2 : ZMod 915464440000220221)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (17, 1), (43, 1), (149, 1), (48491, 1), (87541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (17, 1), (43, 1), (149, 1), (48491, 1), (87541, 1)] : List FactorBlock).map factorBlockValue).prod) = 915464440000220221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_43
      · exact prime_oneHundredTwentyNineDW_149
      · exact prime_oneHundredTwentyNineDW_48491
      · exact prime_oneHundredTwentyNineDW_87541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 915464440000220221) ^ 457732220000110110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 305154813333406740 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 183092888000044044 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 83224040000020020 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 53850849411777660 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 21289870697679540 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 6144056644296780 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 18879058794420 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 915464440000220221) ^ 10457550633420 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2665425117139169443 : Nat.Prime 2665425117139169443 := by
  apply lucas_primality 2665425117139169443 (2 : ZMod 2665425117139169443)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (22031, 1), (1061273754263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (22031, 1), (1061273754263, 1)] : List FactorBlock).map factorBlockValue).prod) = 2665425117139169443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_22031
      · exact prime_oneHundredTwentyNineDW_1061273754263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2665425117139169443) ^ 1332712558569584721 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2665425117139169443) ^ 888475039046389814 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2665425117139169443) ^ 140285532481008918 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2665425117139169443) ^ 120985207985982 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2665425117139169443) ^ 2511534 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2986143385478211733 : Nat.Prime 2986143385478211733 := by
  apply lucas_primality 2986143385478211733 (2 : ZMod 2986143385478211733)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (229, 1), (14731, 1), (73766928289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (229, 1), (14731, 1), (73766928289, 1)] : List FactorBlock).map factorBlockValue).prod) = 2986143385478211733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_229
      · exact prime_oneHundredTwentyNineDW_14731
      · exact prime_oneHundredTwentyNineDW_73766928289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2986143385478211733) ^ 1493071692739105866 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986143385478211733) ^ 995381128492737244 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986143385478211733) ^ 13039927447503108 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986143385478211733) ^ 202711518938172 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 2986143385478211733) ^ 40480788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3130104340067660551 : Nat.Prime 3130104340067660551 := by
  apply lucas_primality 3130104340067660551 (6 : ZMod 3130104340067660551)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (7, 1), (47, 1), (21142211010251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (7, 1), (47, 1), (21142211010251, 1)] : List FactorBlock).map factorBlockValue).prod) = 3130104340067660551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_21142211010251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3130104340067660551) ^ 1565052170033830275 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3130104340067660551) ^ 1043368113355886850 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3130104340067660551) ^ 626020868013532110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3130104340067660551) ^ 447157762866808650 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3130104340067660551) ^ 66597964682290650 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 3130104340067660551) ^ 148050 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6657005320046945599 : Nat.Prime 6657005320046945599 := by
  apply lucas_primality 6657005320046945599 (3 : ZMod 6657005320046945599)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (22642875238254917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (22642875238254917, 1)] : List FactorBlock).map factorBlockValue).prod) = 6657005320046945599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_22642875238254917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6657005320046945599) ^ 3328502660023472799 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6657005320046945599) ^ 2219001773348981866 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6657005320046945599) ^ 951000760006706514 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6657005320046945599) ^ 294 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6709399084962554977 : Nat.Prime 6709399084962554977 := by
  apply lucas_primality 6709399084962554977 (5 : ZMod 6709399084962554977)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (271, 1), (521, 1), (1129, 1), (146147093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (271, 1), (521, 1), (1129, 1), (146147093, 1)] : List FactorBlock).map factorBlockValue).prod) = 6709399084962554977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_271
      · exact prime_oneHundredTwentyNineDW_521
      · exact prime_oneHundredTwentyNineDW_1129
      · exact prime_oneHundredTwentyNineDW_146147093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6709399084962554977) ^ 3354699542481277488 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6709399084962554977) ^ 2236466361654184992 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6709399084962554977) ^ 24757930202813856 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6709399084962554977) ^ 12877925307029856 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6709399084962554977) ^ 5942780411835744 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 6709399084962554977) ^ 45908536032 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6735751439230410043 : Nat.Prime 6735751439230410043 := by
  apply lucas_primality 6735751439230410043 (2 : ZMod 6735751439230410043)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (181, 1), (6202349391556547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (181, 1), (6202349391556547, 1)] : List FactorBlock).map factorBlockValue).prod) = 6735751439230410043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_181
      · exact prime_oneHundredTwentyNineDW_6202349391556547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6735751439230410043) ^ 3367875719615205021 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6735751439230410043) ^ 2245250479743470014 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6735751439230410043) ^ 37214096349339282 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 6735751439230410043) ^ 1086 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_10024582864675573813 : Nat.Prime 10024582864675573813 := by
  apply lucas_primality 10024582864675573813 (2 : ZMod 10024582864675573813)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (31, 1), (127, 1), (11167759386517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (31, 1), (127, 1), (11167759386517, 1)] : List FactorBlock).map factorBlockValue).prod) = 10024582864675573813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_127
      · exact prime_oneHundredTwentyNineDW_11167759386517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10024582864675573813) ^ 5012291432337786906 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10024582864675573813) ^ 3341527621558524604 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10024582864675573813) ^ 527609624456609148 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10024582864675573813) ^ 323373640795986252 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10024582864675573813) ^ 78933723343902156 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 10024582864675573813) ^ 897636 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_13308756922535047349 : Nat.Prime 13308756922535047349 := by
  apply lucas_primality 13308756922535047349 (2 : ZMod 13308756922535047349)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (3007541, 1), (3603525251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (3007541, 1), (3603525251, 1)] : List FactorBlock).map factorBlockValue).prod) = 13308756922535047349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_307
      · exact prime_oneHundredTwentyNineDW_3007541
      · exact prime_oneHundredTwentyNineDW_3603525251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13308756922535047349) ^ 6654378461267523674 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13308756922535047349) ^ 43350999747671164 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13308756922535047349) ^ 4425129008228 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 13308756922535047349) ^ 3693260348 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_21010470436619543021 : Nat.Prime 21010470436619543021 := by
  apply lucas_primality 21010470436619543021 (2 : ZMod 21010470436619543021)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (157, 1), (821, 1), (1597, 1), (5103381739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (157, 1), (821, 1), (1597, 1), (5103381739, 1)] : List FactorBlock).map factorBlockValue).prod) = 21010470436619543021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_157
      · exact prime_oneHundredTwentyNineDW_821
      · exact prime_oneHundredTwentyNineDW_1597
      · exact prime_oneHundredTwentyNineDW_5103381739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21010470436619543021) ^ 10505235218309771510 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21010470436619543021) ^ 4202094087323908604 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21010470436619543021) ^ 133824652462544860 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21010470436619543021) ^ 25591316000754620 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21010470436619543021) ^ 13156211920237660 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 21010470436619543021) ^ 4116970180 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_22260499770492309961 : Nat.Prime 22260499770492309961 := by
  apply lucas_primality 22260499770492309961 (14 : ZMod 22260499770492309961)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (17, 1), (2837, 1), (5657, 1), (226640737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (17, 1), (2837, 1), (5657, 1), (226640737, 1)] : List FactorBlock).map factorBlockValue).prod) = 22260499770492309961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_2837
      · exact prime_oneHundredTwentyNineDW_5657
      · exact prime_oneHundredTwentyNineDW_226640737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 22260499770492309961) ^ 11130249885246154980 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 7420166590164103320 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 4452099954098461992 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 1309441162970135880 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 7846492693159080 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 3935036197718280 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (14 : ZMod 22260499770492309961) ^ 98219323080 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_26617513845070094699 : Nat.Prime 26617513845070094699 := by
  apply lucas_primality 26617513845070094699 (2 : ZMod 26617513845070094699)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13308756922535047349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13308756922535047349, 1)] : List FactorBlock).map factorBlockValue).prod) = 26617513845070094699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_13308756922535047349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 26617513845070094699) ^ 13308756922535047349 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 26617513845070094699) ^ 2 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_37882629138159203597 : Nat.Prime 37882629138159203597 := by
  apply lucas_primality 37882629138159203597 (3 : ZMod 37882629138159203597)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (373, 1), (601, 1), (3840644698733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (373, 1), (601, 1), (3840644698733, 1)] : List FactorBlock).map factorBlockValue).prod) = 37882629138159203597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_373
      · exact prime_oneHundredTwentyNineDW_601
      · exact prime_oneHundredTwentyNineDW_3840644698733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37882629138159203597) ^ 18941314569079601798 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37882629138159203597) ^ 3443875376196291236 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37882629138159203597) ^ 101562008413295452 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37882629138159203597) ^ 63032660795605996 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 37882629138159203597) ^ 9863612 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_52890648300701414633 : Nat.Prime 52890648300701414633 := by
  apply lucas_primality 52890648300701414633 (3 : ZMod 52890648300701414633)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13, 1), (19, 1), (61, 1), (39890495408917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13, 1), (19, 1), (61, 1), (39890495408917, 1)] : List FactorBlock).map factorBlockValue).prod) = 52890648300701414633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_61
      · exact prime_oneHundredTwentyNineDW_39890495408917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 52890648300701414633) ^ 26445324150350707316 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 52890648300701414633) ^ 4808240754609219512 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 52890648300701414633) ^ 4068511407746262664 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 52890648300701414633) ^ 2783718331615863928 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 52890648300701414633) ^ 867059808208219912 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 52890648300701414633) ^ 1325896 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_67820065799057365253 : Nat.Prime 67820065799057365253 := by
  apply lucas_primality 67820065799057365253 (2 : ZMod 67820065799057365253)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (643, 1), (11903, 1), (87973, 1), (25181489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (643, 1), (11903, 1), (87973, 1), (25181489, 1)] : List FactorBlock).map factorBlockValue).prod) = 67820065799057365253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_643
      · exact prime_oneHundredTwentyNineDW_11903
      · exact prime_oneHundredTwentyNineDW_87973
      · exact prime_oneHundredTwentyNineDW_25181489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67820065799057365253) ^ 33910032899528682626 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67820065799057365253) ^ 105474441367118764 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67820065799057365253) ^ 5697728790981884 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67820065799057365253) ^ 770919097894324 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 67820065799057365253) ^ 2693250816068 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_68646863428735418129 : Nat.Prime 68646863428735418129 := by
  apply lucas_primality 68646863428735418129 (3 : ZMod 68646863428735418129)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (127, 1), (33782905230676879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (127, 1), (33782905230676879, 1)] : List FactorBlock).map factorBlockValue).prod) = 68646863428735418129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_127
      · exact prime_oneHundredTwentyNineDW_33782905230676879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68646863428735418129) ^ 34323431714367709064 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68646863428735418129) ^ 540526483690830064 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 68646863428735418129) ^ 2032 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_193596969384820842851 : Nat.Prime 193596969384820842851 := by
  apply lucas_primality 193596969384820842851 (2 : ZMod 193596969384820842851)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4253, 1), (910401925157869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4253, 1), (910401925157869, 1)] : List FactorBlock).map factorBlockValue).prod) = 193596969384820842851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_4253
      · exact prime_oneHundredTwentyNineDW_910401925157869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 193596969384820842851) ^ 96798484692410421425 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 193596969384820842851) ^ 38719393876964168570 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 193596969384820842851) ^ 45520096257893450 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 193596969384820842851) ^ 212650 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_6863
      · exact prime_oneHundredTwentyNineDW_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_291426551646771307093 : Nat.Prime 291426551646771307093 := by
  apply lucas_primality 291426551646771307093 (5 : ZMod 291426551646771307093)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (173, 1), (2648658083822039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (173, 1), (2648658083822039, 1)] : List FactorBlock).map factorBlockValue).prod) = 291426551646771307093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_53
      · exact prime_oneHundredTwentyNineDW_173
      · exact prime_oneHundredTwentyNineDW_2648658083822039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 291426551646771307093) ^ 145713275823385653546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 291426551646771307093) ^ 97142183882257102364 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 291426551646771307093) ^ 5498614182014552964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 291426551646771307093) ^ 1684546541310816804 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 291426551646771307093) ^ 110028 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_474783269368627324577 : Nat.Prime 474783269368627324577 := by
  apply lucas_primality 474783269368627324577 (3 : ZMod 474783269368627324577)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (199, 1), (43777, 1), (67079, 1), (25389829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (199, 1), (43777, 1), (67079, 1), (25389829, 1)] : List FactorBlock).map factorBlockValue).prod) = 474783269368627324577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_199
      · exact prime_oneHundredTwentyNineDW_43777
      · exact prime_oneHundredTwentyNineDW_67079
      · exact prime_oneHundredTwentyNineDW_25389829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 474783269368627324577) ^ 237391634684313662288 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474783269368627324577) ^ 2385845574716720224 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474783269368627324577) ^ 10845495793878688 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474783269368627324577) ^ 7077971785038944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 474783269368627324577) ^ 18699742694944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_556328431354272232111 : Nat.Prime 556328431354272232111 := by
  apply lucas_primality 556328431354272232111 (12 : ZMod 556328431354272232111)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (17, 1), (23, 1), (3169, 1), (20129, 1), (1167211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (13, 1), (17, 1), (23, 1), (3169, 1), (20129, 1), (1167211, 1)] : List FactorBlock).map factorBlockValue).prod) = 556328431354272232111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_3169
      · exact prime_oneHundredTwentyNineDW_20129
      · exact prime_oneHundredTwentyNineDW_1167211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 556328431354272232111) ^ 278164215677136116055 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 185442810451424077370 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 111265686270854446422 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 79475490193467461730 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 42794494719559402470 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 32725201844368954830 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 24188192667577053570 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 175553307464270190 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 27638155464964590 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (12 : ZMod 556328431354272232111) ^ 476630558960010 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_704824522373402356091 : Nat.Prime 704824522373402356091 := by
  apply lucas_primality 704824522373402356091 (6 : ZMod 704824522373402356091)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (337236613575790601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (337236613575790601, 1)] : List FactorBlock).map factorBlockValue).prod) = 704824522373402356091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_337236613575790601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 704824522373402356091) ^ 352412261186701178045 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 704824522373402356091) ^ 140964904474680471218 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 704824522373402356091) ^ 64074956579400214190 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 704824522373402356091) ^ 37096027493336966110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 704824522373402356091) ^ 2090 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_1549
      · exact prime_oneHundredTwentyNineDW_47713
      · exact prime_oneHundredTwentyNineDW_341461
      · exact prime_oneHundredTwentyNineDW_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1449414091918837687327 : Nat.Prime 1449414091918837687327 := by
  apply lucas_primality 1449414091918837687327 (3 : ZMod 1449414091918837687327)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (12409, 1), (414196654315427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (12409, 1), (414196654315427, 1)] : List FactorBlock).map factorBlockValue).prod) = 1449414091918837687327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_47
      · exact prime_oneHundredTwentyNineDW_12409
      · exact prime_oneHundredTwentyNineDW_414196654315427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1449414091918837687327) ^ 724707045959418843663 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1449414091918837687327) ^ 483138030639612562442 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1449414091918837687327) ^ 30838597700400801858 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1449414091918837687327) ^ 116803456516950414 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1449414091918837687327) ^ 3499338 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1777397300001137361733 : Nat.Prime 1777397300001137361733 := by
  apply lucas_primality 1777397300001137361733 (2 : ZMod 1777397300001137361733)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (378502067, 1), (20595930307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (378502067, 1), (20595930307, 1)] : List FactorBlock).map factorBlockValue).prod) = 1777397300001137361733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_378502067
      · exact prime_oneHundredTwentyNineDW_20595930307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1777397300001137361733) ^ 888698650000568680866 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1777397300001137361733) ^ 592465766667045787244 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1777397300001137361733) ^ 93547226315849334828 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1777397300001137361733) ^ 4695872109996 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1777397300001137361733) ^ 86298471276 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2248086279757156496477 : Nat.Prime 2248086279757156496477 := by
  apply lucas_primality 2248086279757156496477 (5 : ZMod 2248086279757156496477)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (101, 1), (61149120872515409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (101, 1), (61149120872515409, 1)] : List FactorBlock).map factorBlockValue).prod) = 2248086279757156496477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_101
      · exact prime_oneHundredTwentyNineDW_61149120872515409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2248086279757156496477) ^ 1124043139878578248238 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248086279757156496477) ^ 321155182822450928068 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248086279757156496477) ^ 172929713827473576652 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248086279757156496477) ^ 22258279997595608876 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 2248086279757156496477) ^ 36764 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_2304834551137845547759 : Nat.Prime 2304834551137845547759 := by
  apply lucas_primality 2304834551137845547759 (6 : ZMod 2304834551137845547759)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (599, 1), (241663, 1), (126366578209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (599, 1), (241663, 1), (126366578209, 1)] : List FactorBlock).map factorBlockValue).prod) = 2304834551137845547759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_599
      · exact prime_oneHundredTwentyNineDW_241663
      · exact prime_oneHundredTwentyNineDW_126366578209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2304834551137845547759) ^ 1152417275568922773879 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2304834551137845547759) ^ 768278183712615182586 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2304834551137845547759) ^ 329262078733977935394 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2304834551137845547759) ^ 3847803925104917442 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2304834551137845547759) ^ 9537391123746066 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 2304834551137845547759) ^ 18239273262 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3001432778053770845347 : Nat.Prime 3001432778053770845347 := by
  apply lucas_primality 3001432778053770845347 (5 : ZMod 3001432778053770845347)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (631, 1), (1933, 1), (1943719994347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (631, 1), (1933, 1), (1943719994347, 1)] : List FactorBlock).map factorBlockValue).prod) = 3001432778053770845347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_211
      · exact prime_oneHundredTwentyNineDW_631
      · exact prime_oneHundredTwentyNineDW_1933
      · exact prime_oneHundredTwentyNineDW_1943719994347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 3001432778053770845347) ^ 1500716389026885422673 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3001432778053770845347) ^ 1000477592684590281782 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3001432778053770845347) ^ 14224799895989435286 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3001432778053770845347) ^ 4756628808326102766 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3001432778053770845347) ^ 1552732942604123562 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 3001432778053770845347) ^ 1544169318 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3140834758214232146581 : Nat.Prime 3140834758214232146581 := by
  apply lucas_primality 3140834758214232146581 (11 : ZMod 3140834758214232146581)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (71, 1), (1974743, 1), (124452507577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (71, 1), (1974743, 1), (124452507577, 1)] : List FactorBlock).map factorBlockValue).prod) = 3140834758214232146581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_71
      · exact prime_oneHundredTwentyNineDW_1974743
      · exact prime_oneHundredTwentyNineDW_124452507577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 3140834758214232146581) ^ 1570417379107116073290 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140834758214232146581) ^ 1046944919404744048860 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140834758214232146581) ^ 628166951642846429316 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140834758214232146581) ^ 44237109270622987980 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140834758214232146581) ^ 1590503046834060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 3140834758214232146581) ^ 25237215540 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4047725296058725747979 : Nat.Prime 4047725296058725747979 := by
  apply lucas_primality 4047725296058725747979 (2 : ZMod 4047725296058725747979)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1531, 1), (2551, 1), (2663, 1), (6277150273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1531, 1), (2551, 1), (2663, 1), (6277150273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4047725296058725747979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_1531
      · exact prime_oneHundredTwentyNineDW_2551
      · exact prime_oneHundredTwentyNineDW_2663
      · exact prime_oneHundredTwentyNineDW_6277150273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4047725296058725747979) ^ 2023862648029362873989 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4047725296058725747979) ^ 130571783743829862838 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4047725296058725747979) ^ 2643844086256515838 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4047725296058725747979) ^ 1586721009823099078 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4047725296058725747979) ^ 1519986968103164006 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4047725296058725747979) ^ 644834856586 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_4228947134240414136547 : Nat.Prime 4228947134240414136547 := by
  apply lucas_primality 4228947134240414136547 (2 : ZMod 4228947134240414136547)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (704824522373402356091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (704824522373402356091, 1)] : List FactorBlock).map factorBlockValue).prod) = 4228947134240414136547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_704824522373402356091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4228947134240414136547) ^ 2114473567120207068273 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4228947134240414136547) ^ 1409649044746804712182 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 4228947134240414136547) ^ 6 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5196052304933063713093 : Nat.Prime 5196052304933063713093 := by
  apply lucas_primality 5196052304933063713093 (5 : ZMod 5196052304933063713093)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (6673, 1), (12503, 1), (101762258239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (6673, 1), (12503, 1), (101762258239, 1)] : List FactorBlock).map factorBlockValue).prod) = 5196052304933063713093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_6673
      · exact prime_oneHundredTwentyNineDW_12503
      · exact prime_oneHundredTwentyNineDW_101762258239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5196052304933063713093) ^ 2598026152466531856546 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5196052304933063713093) ^ 1732017434977687904364 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5196052304933063713093) ^ 305650135584297865476 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5196052304933063713093) ^ 778668111034476804 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5196052304933063713093) ^ 415584444128054364 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5196052304933063713093) ^ 51060701628 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_6006694182932220990089 : Nat.Prime 6006694182932220990089 := by
  apply lucas_primality 6006694182932220990089 (3 : ZMod 6006694182932220990089)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (367, 1), (1699, 1), (1204165253268917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (367, 1), (1699, 1), (1204165253268917, 1)] : List FactorBlock).map factorBlockValue).prod) = 6006694182932220990089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_367
      · exact prime_oneHundredTwentyNineDW_1699
      · exact prime_oneHundredTwentyNineDW_1204165253268917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6006694182932220990089) ^ 3003347091466110495044 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006694182932220990089) ^ 16367014122431119864 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006694182932220990089) ^ 3535429183597540312 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 6006694182932220990089) ^ 4988264 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_7794029730766277381017 : Nat.Prime 7794029730766277381017 := by
  apply lucas_primality 7794029730766277381017 (5 : ZMod 7794029730766277381017)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 2), (43, 1), (14276662363473347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 2), (43, 1), (14276662363473347, 1)] : List FactorBlock).map factorBlockValue).prod) = 7794029730766277381017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_43
      · exact prime_oneHundredTwentyNineDW_14276662363473347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7794029730766277381017) ^ 3897014865383138690508 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7794029730766277381017) ^ 2598009910255425793672 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7794029730766277381017) ^ 338870857859403364392 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7794029730766277381017) ^ 181256505366657613512 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 7794029730766277381017) ^ 545928 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_12005731112215083381389 : Nat.Prime 12005731112215083381389 := by
  apply lucas_primality 12005731112215083381389 (2 : ZMod 12005731112215083381389)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3001432778053770845347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3001432778053770845347, 1)] : List FactorBlock).map factorBlockValue).prod) = 12005731112215083381389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3001432778053770845347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 12005731112215083381389) ^ 6002865556107541690694 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 12005731112215083381389) ^ 4 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_14669189887073187151199 : Nat.Prime 14669189887073187151199 := by
  apply lucas_primality 14669189887073187151199 (13 : ZMod 14669189887073187151199)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (463, 1), (2473, 1), (612971, 1), (16614239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (463, 1), (2473, 1), (612971, 1), (16614239, 1)] : List FactorBlock).map factorBlockValue).prod) = 14669189887073187151199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_17
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_463
      · exact prime_oneHundredTwentyNineDW_2473
      · exact prime_oneHundredTwentyNineDW_612971
      · exact prime_oneHundredTwentyNineDW_16614239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 14669189887073187151199) ^ 7334594943536593575599 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 862893522769011008894 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 396464591542518571654 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 31682915522836257346 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 5931738733147265326 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 23931295097277338 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 14669189887073187151199) ^ 882928786992482 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_16837860974240292704177 : Nat.Prime 16837860974240292704177 := by
  apply lucas_primality 16837860974240292704177 (3 : ZMod 16837860974240292704177)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (49739, 1), (1470709, 1), (14386102061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (49739, 1), (1470709, 1), (14386102061, 1)] : List FactorBlock).map factorBlockValue).prod) = 16837860974240292704177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_49739
      · exact prime_oneHundredTwentyNineDW_1470709
      · exact prime_oneHundredTwentyNineDW_14386102061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16837860974240292704177) ^ 8418930487120146352088 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16837860974240292704177) ^ 338524316416499984 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16837860974240292704177) ^ 11448805286593264 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 16837860974240292704177) ^ 1170425519216 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_16915788536961656546189 : Nat.Prime 16915788536961656546189 := by
  apply lucas_primality 16915788536961656546189 (2 : ZMod 16915788536961656546189)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (4228947134240414136547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (4228947134240414136547, 1)] : List FactorBlock).map factorBlockValue).prod) = 16915788536961656546189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_4228947134240414136547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 16915788536961656546189) ^ 8457894268480828273094 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 16915788536961656546189) ^ 4 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_55503851307387340238893 : Nat.Prime 55503851307387340238893 := by
  apply lucas_primality 55503851307387340238893 (6 : ZMod 55503851307387340238893)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (359, 1), (1097, 1), (12289, 1), (45509803243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (359, 1), (1097, 1), (12289, 1), (45509803243, 1)] : List FactorBlock).map factorBlockValue).prod) = 55503851307387340238893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_359
      · exact prime_oneHundredTwentyNineDW_1097
      · exact prime_oneHundredTwentyNineDW_12289
      · exact prime_oneHundredTwentyNineDW_45509803243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 55503851307387340238893) ^ 27751925653693670119446 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 18501283769129113412964 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 7929121615341048605556 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 154606828154282284788 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 50596035831711340236 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 4516547425127133228 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (6 : ZMod 55503851307387340238893) ^ 1219602093444 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_62767172130709739333317 : Nat.Prime 62767172130709739333317 := by
  apply lucas_primality 62767172130709739333317 (2 : ZMod 62767172130709739333317)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (31, 1), (347, 1), (37403892117184123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (31, 1), (347, 1), (37403892117184123, 1)] : List FactorBlock).map factorBlockValue).prod) = 62767172130709739333317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_347
      · exact prime_oneHundredTwentyNineDW_37403892117184123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 62767172130709739333317) ^ 31383586065354869666658 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 62767172130709739333317) ^ 20922390710236579777772 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 62767172130709739333317) ^ 4828244010054595333332 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 62767172130709739333317) ^ 2024747488087410946236 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 62767172130709739333317) ^ 180885222278702418828 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 62767172130709739333317) ^ 1678092 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_70614340094131242678221 : Nat.Prime 70614340094131242678221 := by
  apply lucas_primality 70614340094131242678221 (2 : ZMod 70614340094131242678221)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (378733, 1), (4359863, 1), (305463187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (378733, 1), (4359863, 1), (305463187, 1)] : List FactorBlock).map factorBlockValue).prod) = 70614340094131242678221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_378733
      · exact prime_oneHundredTwentyNineDW_4359863
      · exact prime_oneHundredTwentyNineDW_305463187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70614340094131242678221) ^ 35307170047065621339110 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70614340094131242678221) ^ 14122868018826248535644 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70614340094131242678221) ^ 10087762870590177525460 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70614340094131242678221) ^ 186448870560873340 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70614340094131242678221) ^ 16196458488289940 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 70614340094131242678221) ^ 231171359101060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_82336607840432290352429 : Nat.Prime 82336607840432290352429 := by
  apply lucas_primality 82336607840432290352429 (2 : ZMod 82336607840432290352429)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (556328431354272232111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (556328431354272232111, 1)] : List FactorBlock).map factorBlockValue).prod) = 82336607840432290352429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_37
      · exact prime_oneHundredTwentyNineDW_556328431354272232111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 82336607840432290352429) ^ 41168303920216145176214 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82336607840432290352429) ^ 2225313725417088928444 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 82336607840432290352429) ^ 148 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_88780682460732502112497 : Nat.Prime 88780682460732502112497 := by
  apply lucas_primality 88780682460732502112497 (5 : ZMod 88780682460732502112497)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (13, 1), (73847, 1), (281683, 1), (2279917543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (13, 1), (73847, 1), (281683, 1), (2279917543, 1)] : List FactorBlock).map factorBlockValue).prod) = 88780682460732502112497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_73847
      · exact prime_oneHundredTwentyNineDW_281683
      · exact prime_oneHundredTwentyNineDW_2279917543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88780682460732502112497) ^ 44390341230366251056248 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 88780682460732502112497) ^ 29593560820244167370832 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 88780682460732502112497) ^ 6829283266210192470192 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 88780682460732502112497) ^ 1202224632831834768 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 88780682460732502112497) ^ 315179412533708112 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 88780682460732502112497) ^ 38940304105872 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_95236459446477158318783 : Nat.Prime 95236459446477158318783 := by
  apply lucas_primality 95236459446477158318783 (5 : ZMod 95236459446477158318783)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (505283, 1), (1035612220688047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (505283, 1), (1035612220688047, 1)] : List FactorBlock).map factorBlockValue).prod) = 95236459446477158318783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_505283
      · exact prime_oneHundredTwentyNineDW_1035612220688047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 95236459446477158318783) ^ 47618229723238579159391 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95236459446477158318783) ^ 13605208492353879759826 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95236459446477158318783) ^ 7325881495882858332214 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95236459446477158318783) ^ 188481424165224554 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 95236459446477158318783) ^ 91961506 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_142662175481002775511031 : Nat.Prime 142662175481002775511031 := by
  apply lucas_primality 142662175481002775511031 (33 : ZMod 142662175481002775511031)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (616415557, 1), (593431567061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (616415557, 1), (593431567061, 1)] : List FactorBlock).map factorBlockValue).prod) = 142662175481002775511031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_616415557
      · exact prime_oneHundredTwentyNineDW_593431567061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 142662175481002775511031) ^ 71331087740501387755515 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (33 : ZMod 142662175481002775511031) ^ 47554058493667591837010 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (33 : ZMod 142662175481002775511031) ^ 28532435096200555102206 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (33 : ZMod 142662175481002775511031) ^ 10974013498538675039310 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (33 : ZMod 142662175481002775511031) ^ 231438311153790 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (33 : ZMod 142662175481002775511031) ^ 240402067230 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_190739719715832349257821 : Nat.Prime 190739719715832349257821 := by
  apply lucas_primality 190739719715832349257821 (2 : ZMod 190739719715832349257821)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (139591, 1), (68320923166906301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (139591, 1), (68320923166906301, 1)] : List FactorBlock).map factorBlockValue).prod) = 190739719715832349257821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_139591
      · exact prime_oneHundredTwentyNineDW_68320923166906301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190739719715832349257821) ^ 95369859857916174628910 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 190739719715832349257821) ^ 38147943943166469851564 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 190739719715832349257821) ^ 1366418463338126020 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 190739719715832349257821) ^ 2791820 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_200150170014388762515211 : Nat.Prime 200150170014388762515211 := by
  apply lucas_primality 200150170014388762515211 (3 : ZMod 200150170014388762515211)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 1), (31, 1), (71479, 1), (158467769756897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 1), (31, 1), (71479, 1), (158467769756897, 1)] : List FactorBlock).map factorBlockValue).prod) = 200150170014388762515211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_31
      · exact prime_oneHundredTwentyNineDW_71479
      · exact prime_oneHundredTwentyNineDW_158467769756897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 200150170014388762515211) ^ 100075085007194381257605 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 66716723338129587505070 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 40030034002877752503042 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 10534219474441513816590 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 6456457097238347177910 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 2800125491604369990 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 200150170014388762515211) ^ 1263033930 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_302616032479987485910087 : Nat.Prime 302616032479987485910087 := by
  apply lucas_primality 302616032479987485910087 (3 : ZMod 302616032479987485910087)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (179, 1), (2999, 1), (1470871, 1), (21291945497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (179, 1), (2999, 1), (1470871, 1), (21291945497, 1)] : List FactorBlock).map factorBlockValue).prod) = 302616032479987485910087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_179
      · exact prime_oneHundredTwentyNineDW_2999
      · exact prime_oneHundredTwentyNineDW_1470871
      · exact prime_oneHundredTwentyNineDW_21291945497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 302616032479987485910087) ^ 151308016239993742955043 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 302616032479987485910087) ^ 100872010826662495303362 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 302616032479987485910087) ^ 1690592360223393776034 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 302616032479987485910087) ^ 100905646042009831914 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 302616032479987485910087) ^ 205739342525610666 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 302616032479987485910087) ^ 14212699939638 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_318823538860406583219679 : Nat.Prime 318823538860406583219679 := by
  apply lucas_primality 318823538860406583219679 (11 : ZMod 318823538860406583219679)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (41, 1), (2847601, 1), (5910788354209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (41, 1), (2847601, 1), (5910788354209, 1)] : List FactorBlock).map factorBlockValue).prod) = 318823538860406583219679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_41
      · exact prime_oneHundredTwentyNineDW_2847601
      · exact prime_oneHundredTwentyNineDW_5910788354209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 318823538860406583219679) ^ 159411769430203291609839 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 106274512953468861073226 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 45546219837200940459954 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 28983958078218780292698 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 7776183874644063005358 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 111962153005426878 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (11 : ZMod 318823538860406583219679) ^ 53939258142 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_493924184927193713097043 : Nat.Prime 493924184927193713097043 := by
  apply lucas_primality 493924184927193713097043 (3 : ZMod 493924184927193713097043)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (563, 1), (1000639879, 1), (4428013127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (563, 1), (1000639879, 1), (4428013127, 1)] : List FactorBlock).map factorBlockValue).prod) = 493924184927193713097043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_563
      · exact prime_oneHundredTwentyNineDW_1000639879
      · exact prime_oneHundredTwentyNineDW_4428013127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 493924184927193713097043) ^ 246962092463596856548521 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 493924184927193713097043) ^ 164641394975731237699014 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 493924184927193713097043) ^ 44902198629744883008822 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 493924184927193713097043) ^ 877307610883114943334 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 493924184927193713097043) ^ 493608335319198 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 493924184927193713097043) ^ 111545329871646 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1014247709312124048340531 : Nat.Prime 1014247709312124048340531 := by
  apply lucas_primality 1014247709312124048340531 (2 : ZMod 1014247709312124048340531)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1543, 1), (3130104340067660551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1543, 1), (3130104340067660551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1014247709312124048340531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_1543
      · exact prime_oneHundredTwentyNineDW_3130104340067660551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1014247709312124048340531) ^ 507123854656062024170265 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014247709312124048340531) ^ 338082569770708016113510 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014247709312124048340531) ^ 202849541862424809668106 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014247709312124048340531) ^ 144892529901732006905790 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014247709312124048340531) ^ 657321911414208715710 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014247709312124048340531) ^ 324030 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1063011793585257702889523 : Nat.Prime 1063011793585257702889523 := by
  apply lucas_primality 1063011793585257702889523 (2 : ZMod 1063011793585257702889523)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (263, 1), (1663, 1), (2939, 1), (192547, 1), (74050117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (263, 1), (1663, 1), (2939, 1), (192547, 1), (74050117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1063011793585257702889523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_263
      · exact prime_oneHundredTwentyNineDW_1663
      · exact prime_oneHundredTwentyNineDW_2939
      · exact prime_oneHundredTwentyNineDW_192547
      · exact prime_oneHundredTwentyNineDW_74050117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1063011793585257702889523) ^ 531505896792628851444761 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 36655579089146817341018 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 4041869937586531189694 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 639213345511279436494 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 361691661648607588598 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 5520791254006853926 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 1063011793585257702889523) ^ 14355302012355466 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_1525917757726658794062569 : Nat.Prime 1525917757726658794062569 := by
  apply lucas_primality 1525917757726658794062569 (3 : ZMod 1525917757726658794062569)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (190739719715832349257821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (190739719715832349257821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1525917757726658794062569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_190739719715832349257821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1525917757726658794062569) ^ 762958878863329397031284 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 1525917757726658794062569) ^ 8 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_9206907820661883075699707 : Nat.Prime 9206907820661883075699707 := by
  apply lucas_primality 9206907820661883075699707 (2 : ZMod 9206907820661883075699707)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (200150170014388762515211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (200150170014388762515211, 1)] : List FactorBlock).map factorBlockValue).prod) = 9206907820661883075699707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_23
      · exact prime_oneHundredTwentyNineDW_200150170014388762515211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9206907820661883075699707) ^ 4603453910330941537849853 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9206907820661883075699707) ^ 400300340028777525030422 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 9206907820661883075699707) ^ 46 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_33824002672269703514962441 : Nat.Prime 33824002672269703514962441 := by
  apply lucas_primality 33824002672269703514962441 (23 : ZMod 33824002672269703514962441)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (11, 1), (19, 1), (83, 1), (3167, 1), (59393, 1), (28794848297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (11, 1), (19, 1), (83, 1), (3167, 1), (59393, 1), (28794848297, 1)] : List FactorBlock).map factorBlockValue).prod) = 33824002672269703514962441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_19
      · exact prime_oneHundredTwentyNineDW_83
      · exact prime_oneHundredTwentyNineDW_3167
      · exact prime_oneHundredTwentyNineDW_59393
      · exact prime_oneHundredTwentyNineDW_28794848297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 33824002672269703514962441) ^ 16912001336134851757481220 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 11274667557423234504987480 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 6764800534453940702992488 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 3074909333842700319542040 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 1780210666961563342892760 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 407518104485177150782680 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 10680139776529745347320 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 569494766593196227080 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (23 : ZMod 33824002672269703514962441) ^ 1174654657784520 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_36652830581414105539285183 : Nat.Prime 36652830581414105539285183 := by
  apply lucas_primality 36652830581414105539285183 (3 : ZMod 36652830581414105539285183)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (8945265269, 1), (97558475480759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (8945265269, 1), (97558475480759, 1)] : List FactorBlock).map factorBlockValue).prod) = 36652830581414105539285183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_8945265269
      · exact prime_oneHundredTwentyNineDW_97558475480759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36652830581414105539285183) ^ 18326415290707052769642591 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36652830581414105539285183) ^ 12217610193804701846428394 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36652830581414105539285183) ^ 5236118654487729362755026 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36652830581414105539285183) ^ 4097455970191878 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 36652830581414105539285183) ^ 375701141298 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_59528660440774431361813289 : Nat.Prime 59528660440774431361813289 := by
  apply lucas_primality 59528660440774431361813289 (3 : ZMod 59528660440774431361813289)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1063011793585257702889523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1063011793585257702889523, 1)] : List FactorBlock).map factorBlockValue).prod) = 59528660440774431361813289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_1063011793585257702889523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 59528660440774431361813289) ^ 29764330220387215680906644 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 59528660440774431361813289) ^ 8504094348682061623116184 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 59528660440774431361813289) ^ 56 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_66862090332864573936416329 : Nat.Prime 66862090332864573936416329 := by
  apply lucas_primality 66862090332864573936416329 (13 : ZMod 66862090332864573936416329)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (887, 1), (3140834758214232146581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (887, 1), (3140834758214232146581, 1)] : List FactorBlock).map factorBlockValue).prod) = 66862090332864573936416329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_887
      · exact prime_oneHundredTwentyNineDW_3140834758214232146581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 66862090332864573936416329) ^ 33431045166432286968208164 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 66862090332864573936416329) ^ 22287363444288191312138776 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 66862090332864573936416329) ^ 75380034197141571517944 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (13 : ZMod 66862090332864573936416329) ^ 21288 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_154834952334278267156310301 : Nat.Prime 154834952334278267156310301 := by
  apply lucas_primality 154834952334278267156310301 (2 : ZMod 154834952334278267156310301)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (29, 1), (2943571, 1), (6046098754867139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (29, 1), (2943571, 1), (6046098754867139, 1)] : List FactorBlock).map factorBlockValue).prod) = 154834952334278267156310301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_2943571
      · exact prime_oneHundredTwentyNineDW_6046098754867139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154834952334278267156310301) ^ 77417476167139133578155150 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 154834952334278267156310301) ^ 51611650778092755718770100 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 154834952334278267156310301) ^ 30966990466855653431262060 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 154834952334278267156310301) ^ 5339136287388905764010700 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 154834952334278267156310301) ^ 52601059167344109300 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 154834952334278267156310301) ^ 25609067700 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_448565964850776744555781313 : Nat.Prime 448565964850776744555781313 := by
  apply lucas_primality 448565964850776744555781313 (3 : ZMod 448565964850776744555781313)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (29, 1), (459542833973, 1), (525923222899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (29, 1), (459542833973, 1), (525923222899, 1)] : List FactorBlock).map factorBlockValue).prod) = 448565964850776744555781313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_29
      · exact prime_oneHundredTwentyNineDW_459542833973
      · exact prime_oneHundredTwentyNineDW_525923222899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 448565964850776744555781313) ^ 224282982425388372277890656 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 448565964850776744555781313) ^ 15467791891406094639854528 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 448565964850776744555781313) ^ 976113501700544 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 448565964850776744555781313) ^ 852911499853888 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_683912233404771718156796621 : Nat.Prime 683912233404771718156796621 := by
  apply lucas_primality 683912233404771718156796621 (2 : ZMod 683912233404771718156796621)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (302616032479987485910087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (302616032479987485910087, 1)] : List FactorBlock).map factorBlockValue).prod) = 683912233404771718156796621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_113
      · exact prime_oneHundredTwentyNineDW_302616032479987485910087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 683912233404771718156796621) ^ 341956116702385859078398310 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 683912233404771718156796621) ^ 136782446680954343631359324 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 683912233404771718156796621) ^ 6052320649599749718201740 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 683912233404771718156796621) ^ 2260 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_856811393535191534544750823 : Nat.Prime 856811393535191534544750823 := by
  apply lucas_primality 856811393535191534544750823 (3 : ZMod 856811393535191534544750823)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (257, 1), (16837860974240292704177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (257, 1), (16837860974240292704177, 1)] : List FactorBlock).map factorBlockValue).prod) = 856811393535191534544750823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_11
      · exact prime_oneHundredTwentyNineDW_257
      · exact prime_oneHundredTwentyNineDW_16837860974240292704177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 856811393535191534544750823) ^ 428405696767595767272375411 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 856811393535191534544750823) ^ 285603797845063844848250274 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 856811393535191534544750823) ^ 77891944866835594049522802 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 856811393535191534544750823) ^ 3333896472899577955427046 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (3 : ZMod 856811393535191534544750823) ^ 50886 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_3466191546574183935203764693 : Nat.Prime 3466191546574183935203764693 := by
  apply lucas_primality 3466191546574183935203764693 (2 : ZMod 3466191546574183935203764693)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (173, 1), (181769781169, 1), (706578100511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (173, 1), (181769781169, 1), (706578100511, 1)] : List FactorBlock).map factorBlockValue).prod) = 3466191546574183935203764693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_13
      · exact prime_oneHundredTwentyNineDW_173
      · exact prime_oneHundredTwentyNineDW_181769781169
      · exact prime_oneHundredTwentyNineDW_706578100511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3466191546574183935203764693) ^ 1733095773287091967601882346 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466191546574183935203764693) ^ 1155397182191394645067921564 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466191546574183935203764693) ^ 266630118967244918092597284 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466191546574183935203764693) ^ 20035789286555976504068004 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466191546574183935203764693) ^ 19069129776590868 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (2 : ZMod 3466191546574183935203764693) ^ 4905602854188972 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_5865862617279388198037140247 : Nat.Prime 5865862617279388198037140247 := by
  apply lucas_primality 5865862617279388198037140247 (5 : ZMod 5865862617279388198037140247)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9839, 1), (15937, 1), (24677, 1), (26594759, 1), (28500727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9839, 1), (15937, 1), (24677, 1), (26594759, 1), (28500727, 1)] : List FactorBlock).map factorBlockValue).prod) = 5865862617279388198037140247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_9839
      · exact prime_oneHundredTwentyNineDW_15937
      · exact prime_oneHundredTwentyNineDW_24677
      · exact prime_oneHundredTwentyNineDW_26594759
      · exact prime_oneHundredTwentyNineDW_28500727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5865862617279388198037140247) ^ 2932931308639694099018570123 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5865862617279388198037140247) ^ 596184837613516434397514 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5865862617279388198037140247) ^ 368065672164107937380758 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5865862617279388198037140247) ^ 237705661842176447624798 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5865862617279388198037140247) ^ 220564608887013723194 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 5865862617279388198037140247) ^ 205814490882263747098 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_76256214024632046574482823231 : Nat.Prime 76256214024632046574482823231 := by
  apply lucas_primality 76256214024632046574482823231 (7 : ZMod 76256214024632046574482823231)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (5507, 1), (27235337, 1), (807024761607319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (5507, 1), (27235337, 1), (807024761607319, 1)] : List FactorBlock).map factorBlockValue).prod) = 76256214024632046574482823231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_3
      · exact prime_oneHundredTwentyNineDW_5
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_5507
      · exact prime_oneHundredTwentyNineDW_27235337
      · exact prime_oneHundredTwentyNineDW_807024761607319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 76256214024632046574482823231) ^ 38128107012316023287241411615 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 25418738008210682191494274410 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 15251242804926409314896564646 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 10893744860661720939211831890 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 13847142550323596617846890 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 2799899778168048611790 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (7 : ZMod 76256214024632046574482823231) ^ 94490550541170 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentyNineDW_152512428049264093148965646447 : Nat.Prime 152512428049264093148965646447 := by
  apply lucas_primality 152512428049264093148965646447 (5 : ZMod 152512428049264093148965646447)
  · rw [← oneHundredTwentyNineDWFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (409269811, 1), (26617513845070094699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (409269811, 1), (26617513845070094699, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentyNineDW_2
      · exact prime_oneHundredTwentyNineDW_7
      · exact prime_oneHundredTwentyNineDW_409269811
      · exact prime_oneHundredTwentyNineDW_26617513845070094699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 152512428049264093148965646447) ^ 76256214024632046574482823223 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152512428049264093148965646447) ^ 21787489721323441878423663778 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152512428049264093148965646447) ^ 372645193830981325786 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide
    · change (5 : ZMod 152512428049264093148965646447) ^ 5729777354 ≠ 1
      rw [← oneHundredTwentyNineDWFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646400 : Nat.totient 152512428049264093148965646400 = 39723935482057574318893056000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 2), (43, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_43, prime_oneHundredTwentyNineDW_171401, prime_oneHundredTwentyNineDW_714027719, prime_oneHundredTwentyNineDW_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646401 : Nat.totient 152512428049264093148965646401 = 152508540275239676430672184320 := by
  rw [← show ((([(59497, 1), (115153, 1), (22260499770492309961, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_59497, prime_oneHundredTwentyNineDW_115153, prime_oneHundredTwentyNineDW_22260499770492309961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646402 : Nat.totient 152512428049264093148965646402 = 76252218576195260606718868848 := by
  rw [← show ((([(2, 1), (19087, 1), (296403397, 1), (13478898079334659, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_19087, prime_oneHundredTwentyNineDW_296403397, prime_oneHundredTwentyNineDW_13478898079334659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646403 : Nat.totient 152512428049264093148965646403 = 92607101035945662127391508480 := by
  rw [← show ((([(3, 1), (17, 1), (31, 1), (1405247, 1), (68646863428735418129, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_31, prime_oneHundredTwentyNineDW_1405247, prime_oneHundredTwentyNineDW_68646863428735418129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646404 : Nat.totient 152512428049264093148965646404 = 56836929707800283161104304320 := by
  rw [← show ((([(2, 2), (7, 4), (11, 1), (23, 1), (62767172130709739333317, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_23, prime_oneHundredTwentyNineDW_62767172130709739333317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646405 : Nat.totient 152512428049264093148965646405 = 120639044209407374435472433152 := by
  rw [← show ((([(5, 1), (89, 1), (347191274657, 1), (987134707669897, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_89, prime_oneHundredTwentyNineDW_347191274657, prime_oneHundredTwentyNineDW_987134707669897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646406 : Nat.totient 152512428049264093148965646406 = 46181688587894374222514768640 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (37, 1), (71, 1), (2503, 1), (67820065799057365253, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_37, prime_oneHundredTwentyNineDW_71, prime_oneHundredTwentyNineDW_2503, prime_oneHundredTwentyNineDW_67820065799057365253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646407 : Nat.totient 152512428049264093148965646407 = 151669817949532760671912303680 := by
  rw [← show ((([(181, 1), (18086563013843, 1), (46587629671529, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_181, prime_oneHundredTwentyNineDW_18086563013843, prime_oneHundredTwentyNineDW_46587629671529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646408 : Nat.totient 152512428049264093148965646408 = 75541822891680049949751850752 := by
  rw [← show ((([(2, 3), (107, 1), (44017, 1), (4047725296058725747979, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_107, prime_oneHundredTwentyNineDW_44017, prime_oneHundredTwentyNineDW_4047725296058725747979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646409 : Nat.totient 152512428049264093148965646409 = 93848524150446679131746284992 := by
  rw [← show ((([(3, 1), (13, 2), (17783, 1), (16915788536961656546189, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_17783, prime_oneHundredTwentyNineDW_16915788536961656546189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646410 : Nat.totient 152512428049264093148965646410 = 61004971219704469057241093200 := by
  rw [← show ((([(2, 1), (5, 1), (68101333843331, 1), (223949252448011, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_68101333843331, prime_oneHundredTwentyNineDW_223949252448011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646411 : Nat.totient 152512428049264093148965646411 = 130721974782831088108263135720 := by
  rw [← show ((([(7, 1), (44111, 1), (493924184927193713097043, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_44111, prime_oneHundredTwentyNineDW_493924184927193713097043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646412 : Nat.totient 152512428049264093148965646412 = 50831372345390457747812265216 := by
  rw [← show ((([(2, 2), (3, 1), (8329, 1), (1525917757726658794062569, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_8329, prime_oneHundredTwentyNineDW_1525917757726658794062569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646413 : Nat.totient 152512428049264093148965646413 = 152512428048961312160565426108 := by
  rw [← show ((([(503706268267, 1), (302780484693952039, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_503706268267, prime_oneHundredTwentyNineDW_302780484693952039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646414 : Nat.totient 152512428049264093148965646414 = 76135735968089514488404835640 := by
  rw [← show ((([(2, 1), (691, 1), (7523, 1), (14669189887073187151199, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_691, prime_oneHundredTwentyNineDW_7523, prime_oneHundredTwentyNineDW_14669189887073187151199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646415 : Nat.totient 152512428049264093148965646415 = 73907165427191320362003290880 := by
  rw [← show ((([(3, 4), (5, 1), (11, 1), (1933, 1), (11204590099, 1), (1580628104239, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_1933, prime_oneHundredTwentyNineDW_11204590099, prime_oneHundredTwentyNineDW_1580628104239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646416 : Nat.totient 152512428049264093148965646416 = 76255555331769323116159077632 := by
  rw [← show ((([(2, 4), (115769, 1), (82336607840432290352429, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_115769, prime_oneHundredTwentyNineDW_82336607840432290352429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646417 : Nat.totient 152512428049264093148965646417 = 152510187233154047149662694848 := by
  rw [← show ((([(95443, 1), (237233, 1), (6735751439230410043, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_95443, prime_oneHundredTwentyNineDW_237233, prime_oneHundredTwentyNineDW_6735751439230410043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646418 : Nat.totient 152512428049264093148965646418 = 42860635517357590580505567360 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (61, 1), (59528660440774431361813289, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_61, prime_oneHundredTwentyNineDW_59528660440774431361813289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646419 : Nat.totient 152512428049264093148965646419 = 152352816223156408878129005440 := by
  rw [← show ((([(971, 1), (59879, 1), (2690395889, 1), (974979031919, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_971, prime_oneHundredTwentyNineDW_59879, prime_oneHundredTwentyNineDW_2690395889, prime_oneHundredTwentyNineDW_974979031919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646420 : Nat.totient 152512428049264093148965646420 = 57416443500899423303140007936 := by
  rw [← show ((([(2, 2), (5, 1), (17, 1), (448565964850776744555781313, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_448565964850776744555781313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646421 : Nat.totient 152512428049264093148965646421 = 100666777565167119615875054400 := by
  rw [← show ((([(3, 1), (101, 1), (67807, 1), (14089463, 1), (526858068789827, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_101, prime_oneHundredTwentyNineDW_67807, prime_oneHundredTwentyNineDW_14089463, prime_oneHundredTwentyNineDW_526858068789827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646422 : Nat.totient 152512428049264093148965646422 = 70390351407352658376445682952 := by
  rw [← show ((([(2, 1), (13, 1), (5865862617279388198037140247, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_5865862617279388198037140247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646423 : Nat.totient 152512428049264093148965646423 = 152512428049262935052051291448 := by
  rw [← show ((([(151515197991299, 1), (1006581716363677, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_151515197991299, prime_oneHundredTwentyNineDW_1006581716363677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646424 : Nat.totient 152512428049264093148965646424 = 50613522202257902138607608256 := by
  rw [← show ((([(2, 3), (3, 2), (227, 1), (288684659, 1), (32323856939990219, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_227, prime_oneHundredTwentyNineDW_288684659, prime_oneHundredTwentyNineDW_32323856939990219]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646425 : Nat.totient 152512428049264093148965646425 = 97272717852858479843898470400 := by
  rw [← show ((([(5, 2), (7, 1), (19, 1), (59, 1), (1009, 1), (3571, 1), (215764781356123229, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_59, prime_oneHundredTwentyNineDW_1009, prime_oneHundredTwentyNineDW_3571, prime_oneHundredTwentyNineDW_215764781356123229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646426 : Nat.totient 152512428049264093148965646426 = 69322404309728868676319697600 := by
  rw [← show ((([(2, 1), (11, 1), (48593, 1), (142662175481002775511031, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_48593, prime_oneHundredTwentyNineDW_142662175481002775511031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646427 : Nat.totient 152512428049264093148965646427 = 94882245796301930098699438080 := by
  rw [← show ((([(3, 1), (23, 1), (41, 1), (29936099239, 1), (1800848083149217, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_23, prime_oneHundredTwentyNineDW_41, prime_oneHundredTwentyNineDW_29936099239, prime_oneHundredTwentyNineDW_1800848083149217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646428 : Nat.totient 152512428049264093148965646428 = 73326690127215395119154304000 := by
  rw [← show ((([(2, 2), (29, 1), (401, 1), (631, 1), (5196052304933063713093, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_29, prime_oneHundredTwentyNineDW_401, prime_oneHundredTwentyNineDW_631, prime_oneHundredTwentyNineDW_5196052304933063713093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646429 : Nat.totient 152512428049264093148965646429 = 152512428049251843734689574076 := by
  rw [← show ((([(12463270301347, 1), (12236951005771007, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_12463270301347, prime_oneHundredTwentyNineDW_12236951005771007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646430 : Nat.totient 152512428049264093148965646430 = 40658977204303037424711229440 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3697, 1), (18661009, 1), (69453511, 1), (1060975127, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_3697, prime_oneHundredTwentyNineDW_18661009, prime_oneHundredTwentyNineDW_69453511, prime_oneHundredTwentyNineDW_1060975127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646431 : Nat.totient 152512428049264093148965646431 = 152512425801177813391741308952 := by
  rw [← show ((([(67841003, 1), (2248086279757156496477, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_67841003, prime_oneHundredTwentyNineDW_2248086279757156496477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646432 : Nat.totient 152512428049264093148965646432 = 65353946218454095315067455488 := by
  rw [← show ((([(2, 5), (7, 1), (7669, 1), (88780682460732502112497, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_7669, prime_oneHundredTwentyNineDW_88780682460732502112497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646433 : Nat.totient 152512428049264093148965646433 = 100706187812123590129445644800 := by
  rw [← show ((([(3, 2), (109, 1), (2801, 1), (55503851307387340238893, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_109, prime_oneHundredTwentyNineDW_2801, prime_oneHundredTwentyNineDW_55503851307387340238893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646434 : Nat.totient 152512428049264093148965646434 = 73773753889139739436889304000 := by
  rw [← show ((([(2, 1), (31, 1), (3637, 1), (32191, 1), (21010470436619543021, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_31, prime_oneHundredTwentyNineDW_3637, prime_oneHundredTwentyNineDW_32191, prime_oneHundredTwentyNineDW_21010470436619543021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646435 : Nat.totient 152512428049264093148965646435 = 112574260972893012652359174528 := by
  rw [← show ((([(5, 1), (13, 1), (2239, 1), (232292135107, 1), (4511316316063, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_2239, prime_oneHundredTwentyNineDW_232292135107, prime_oneHundredTwentyNineDW_4511316316063]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646436 : Nat.totient 152512428049264093148965646436 = 50458165148441199164334735360 := by
  rw [← show ((([(2, 2), (3, 1), (137, 1), (6257, 1), (305741, 1), (13419463, 1), (3613669649, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_137, prime_oneHundredTwentyNineDW_6257, prime_oneHundredTwentyNineDW_305741, prime_oneHundredTwentyNineDW_13419463, prime_oneHundredTwentyNineDW_3613669649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646437 : Nat.totient 152512428049264093148965646437 = 127715491122752031024683566080 := by
  rw [← show ((([(11, 1), (17, 1), (47, 1), (124176583, 1), (125928779, 1), (1109688469, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_47, prime_oneHundredTwentyNineDW_124176583, prime_oneHundredTwentyNineDW_125928779, prime_oneHundredTwentyNineDW_1109688469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646438 : Nat.totient 152512428049264093148965646438 = 75755550385345359389723589600 := by
  rw [← show ((([(2, 1), (283, 1), (359, 1), (3877, 1), (193596969384820842851, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_283, prime_oneHundredTwentyNineDW_359, prime_oneHundredTwentyNineDW_3877, prime_oneHundredTwentyNineDW_193596969384820842851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646439 : Nat.totient 152512428049264093148965646439 = 86046794840479440182577055200 := by
  rw [← show ((([(3, 1), (7, 1), (79, 1), (10377571691, 1), (8858559508350031, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_79, prime_oneHundredTwentyNineDW_10377571691, prime_oneHundredTwentyNineDW_8858559508350031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646440 : Nat.totient 152512428049264093148965646440 = 60999870043083870754254552384 := by
  rw [← show ((([(2, 3), (5, 1), (11959, 1), (318823538860406583219679, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_11959, prime_oneHundredTwentyNineDW_318823538860406583219679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646441 : Nat.totient 152512428049264093148965646441 = 152512277897901630586938255360 := by
  rw [← show ((([(1019377, 1), (283484081, 1), (527766389051593, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_1019377, prime_oneHundredTwentyNineDW_283484081, prime_oneHundredTwentyNineDW_527766389051593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646442 : Nat.totient 152512428049264093148965646442 = 49469232870653230801344651264 := by
  rw [← show ((([(2, 1), (3, 3), (67, 1), (83, 1), (8969, 1), (82883, 1), (24098993, 1), (28349813, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_67, prime_oneHundredTwentyNineDW_83, prime_oneHundredTwentyNineDW_8969, prime_oneHundredTwentyNineDW_82883, prime_oneHundredTwentyNineDW_24098993, prime_oneHundredTwentyNineDW_28349813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646443 : Nat.totient 152512428049264093148965646443 = 144934880434372176051795768576 := by
  rw [← show ((([(37, 1), (43, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_37, prime_oneHundredTwentyNineDW_43, prime_oneHundredTwentyNineDW_31177, prime_oneHundredTwentyNineDW_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646444 : Nat.totient 152512428049264093148965646444 = 72241199704977973814660414976 := by
  rw [← show ((([(2, 2), (19, 1), (47237, 1), (20470914953, 1), (2075257924829, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_47237, prime_oneHundredTwentyNineDW_20470914953, prime_oneHundredTwentyNineDW_2075257924829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646445 : Nat.totient 152512428049264093148965646445 = 79804966908858807724711249920 := by
  rw [← show ((([(3, 1), (5, 1), (53, 1), (391049, 1), (1072931, 1), (457230437639509, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_53, prime_oneHundredTwentyNineDW_391049, prime_oneHundredTwentyNineDW_1072931, prime_oneHundredTwentyNineDW_457230437639509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646446 : Nat.totient 152512428049264093148965646446 = 65362469004265242562394804280 := by
  rw [← show ((([(2, 1), (7, 1), (409269811, 1), (26617513845070094699, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_409269811, prime_oneHundredTwentyNineDW_26617513845070094699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646447 : Nat.totient 152512428049264093148965646447 = 152512428049264093148965646446 := by
  rw [← show ((([(152512428049264093148965646447, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_152512428049264093148965646447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646448 : Nat.totient 152512428049264093148965646448 = 42414224704785129948781363200 := by
  rw [← show ((([(2, 4), (3, 1), (11, 1), (13, 1), (173, 1), (181769781169, 1), (706578100511, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_173, prime_oneHundredTwentyNineDW_181769781169, prime_oneHundredTwentyNineDW_706578100511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646449 : Nat.totient 152512428049264093148965646449 = 152445565958931228575029227840 := by
  rw [← show ((([(2281, 1), (66862090332864573936416329, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2281, prime_oneHundredTwentyNineDW_66862090332864573936416329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646450 : Nat.totient 152512428049264093148965646450 = 58271417237012583703748352000 := by
  rw [← show ((([(2, 1), (5, 2), (23, 1), (719, 1), (14752421, 1), (31279981, 1), (399713417, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_23, prime_oneHundredTwentyNineDW_719, prime_oneHundredTwentyNineDW_14752421, prime_oneHundredTwentyNineDW_31279981, prime_oneHundredTwentyNineDW_399713417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646451 : Nat.totient 152512428049264093148965646451 = 101636976018259009740579411456 := by
  rw [← show ((([(3, 2), (3709, 1), (9623, 1), (474783269368627324577, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_3709, prime_oneHundredTwentyNineDW_9623, prime_oneHundredTwentyNineDW_474783269368627324577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646452 : Nat.totient 152512428049264093148965646452 = 75856966482909318209995615200 := by
  rw [← show ((([(2, 2), (191, 1), (218057183, 1), (915464440000220221, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_191, prime_oneHundredTwentyNineDW_218057183, prime_oneHundredTwentyNineDW_915464440000220221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646453 : Nat.totient 152512428049264093148965646453 = 129364112293276502834232864768 := by
  rw [← show ((([(7, 2), (97, 1), (10903, 1), (101203, 1), (96011117, 1), (302884117, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_97, prime_oneHundredTwentyNineDW_10903, prime_oneHundredTwentyNineDW_101203, prime_oneHundredTwentyNineDW_96011117, prime_oneHundredTwentyNineDW_302884117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646454 : Nat.totient 152512428049264093148965646454 = 47620271653415601273710438400 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (211, 1), (34201267, 1), (207195544996051921, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_211, prime_oneHundredTwentyNineDW_34201267, prime_oneHundredTwentyNineDW_207195544996051921]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646455 : Nat.totient 152512428049264093148965646455 = 121973114808128626986869705088 := by
  rw [← show ((([(5, 1), (3313, 1), (9206907820661883075699707, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_3313, prime_oneHundredTwentyNineDW_9206907820661883075699707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646456 : Nat.totient 152512428049264093148965646456 = 76180936419132678497479104000 := by
  rw [← show ((([(2, 3), (1013, 1), (223483179889, 1), (84209475177251, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_1013, prime_oneHundredTwentyNineDW_223483179889, prime_oneHundredTwentyNineDW_84209475177251]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646457 : Nat.totient 152512428049264093148965646457 = 98137559480159373679479211776 := by
  rw [← show ((([(3, 1), (29, 1), (3359, 1), (45989, 1), (1035604699, 1), (10957916839, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_29, prime_oneHundredTwentyNineDW_3359, prime_oneHundredTwentyNineDW_45989, prime_oneHundredTwentyNineDW_1035604699, prime_oneHundredTwentyNineDW_10957916839]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646458 : Nat.totient 152512428049264093148965646458 = 76256211719797495436604190140 := by
  rw [← show ((([(2, 1), (33085331, 1), (2304834551137845547759, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_33085331, prime_oneHundredTwentyNineDW_2304834551137845547759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646459 : Nat.totient 152512428049264093148965646459 = 138052607519211136668272787200 := by
  rw [← show ((([(11, 2), (233, 1), (139003837673, 1), (38916802764131, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_233, prime_oneHundredTwentyNineDW_139003837673, prime_oneHundredTwentyNineDW_38916802764131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646460 : Nat.totient 152512428049264093148965646460 = 34853652152086983285138361344 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (7, 1), (5507, 1), (27235337, 1), (807024761607319, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_5507, prime_oneHundredTwentyNineDW_27235337, prime_oneHundredTwentyNineDW_807024761607319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646461 : Nat.totient 152512428049264093148965646461 = 140780636795881332958940628480 := by
  rw [← show ((([(13, 1), (2135533, 1), (1469455049, 1), (3738516404141, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_2135533, prime_oneHundredTwentyNineDW_1469455049, prime_oneHundredTwentyNineDW_3738516404141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646462 : Nat.totient 152512428049264093148965646462 = 76256214024632046574482823230 := by
  rw [← show ((([(2, 1), (76256214024632046574482823231, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_76256214024632046574482823231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646463 : Nat.totient 152512428049264093148965646463 = 95004136867025361557827191744 := by
  rw [← show ((([(3, 1), (19, 1), (73, 1), (36652830581414105539285183, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_73, prime_oneHundredTwentyNineDW_36652830581414105539285183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646464 : Nat.totient 152512428049264093148965646464 = 76250118891227472036349620480 := by
  rw [← show ((([(2, 7), (12511, 1), (95236459446477158318783, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_12511, prime_oneHundredTwentyNineDW_95236459446477158318783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646465 : Nat.totient 152512428049264093148965646465 = 118073924556915555849746145600 := by
  rw [← show ((([(5, 1), (31, 1), (553591, 1), (1777397300001137361733, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_31, prime_oneHundredTwentyNineDW_553591, prime_oneHundredTwentyNineDW_1777397300001137361733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646466 : Nat.totient 152512428049264093148965646466 = 50837162148187511530543488000 := by
  rw [← show ((([(2, 1), (3, 1), (172553, 1), (4100521, 1), (7431797, 1), (4833910351, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_172553, prime_oneHundredTwentyNineDW_4100521, prime_oneHundredTwentyNineDW_7431797, prime_oneHundredTwentyNineDW_4833910351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646467 : Nat.totient 152512428049264093148965646467 = 130504491550608654427813791360 := by
  rw [← show ((([(7, 1), (593, 1), (122903422531, 1), (298943093867207, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_593, prime_oneHundredTwentyNineDW_122903422531, prime_oneHundredTwentyNineDW_298943093867207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646468 : Nat.totient 152512428049264093148965646468 = 74396306365488235303480166400 := by
  rw [← show ((([(2, 2), (41, 1), (13965858679081, 1), (66587658584977, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_41, prime_oneHundredTwentyNineDW_13965858679081, prime_oneHundredTwentyNineDW_66587658584977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646469 : Nat.totient 152512428049264093148965646469 = 101066119984741874102707770720 := by
  rw [← show ((([(3, 3), (167, 1), (33824002672269703514962441, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_167, prime_oneHundredTwentyNineDW_33824002672269703514962441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646470 : Nat.totient 152512428049264093148965646470 = 55418494836814458001326559200 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (1367, 1), (1014247709312124048340531, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_1367, prime_oneHundredTwentyNineDW_1014247709312124048340531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646471 : Nat.totient 152512428049264093148965646471 = 142132469813341131269195366400 := by
  rw [← show ((([(17, 1), (103, 1), (9601, 1), (616757, 1), (14709182357355053, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_103, prime_oneHundredTwentyNineDW_9601, prime_oneHundredTwentyNineDW_616757, prime_oneHundredTwentyNineDW_14709182357355053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646472 : Nat.totient 152512428049264093148965646472 = 50837475992532217282138395840 := by
  rw [← show ((([(2, 3), (3, 1), (2128057391, 1), (2986143385478211733, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_2128057391, prime_oneHundredTwentyNineDW_2986143385478211733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646473 : Nat.totient 152512428049264093148965646473 = 145881452696146570409421710064 := by
  rw [← show ((([(23, 1), (661471427, 1), (10024582864675573813, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_23, prime_oneHundredTwentyNineDW_661471427, prime_oneHundredTwentyNineDW_10024582864675573813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646474 : Nat.totient 152512428049264093148965646474 = 60329502688101215444622613440 := by
  rw [← show ((([(2, 1), (7, 1), (13, 1), (11867, 1), (70614340094131242678221, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_11867, prime_oneHundredTwentyNineDW_70614340094131242678221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646475 : Nat.totient 152512428049264093148965646475 = 81336189013767866365006288000 := by
  rw [← show ((([(3, 1), (5, 2), (25127, 1), (151901, 1), (532773603223871939, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_25127, prime_oneHundredTwentyNineDW_151901, prime_oneHundredTwentyNineDW_532773603223871939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646476 : Nat.totient 152512428049264093148965646476 = 76256214011213248393192132992 := by
  rw [← show ((([(2, 2), (5682790147, 1), (6709399084962554977, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5682790147, prime_oneHundredTwentyNineDW_6709399084962554977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646477 : Nat.totient 152512428049264093148965646477 = 150364057837326704713292160000 := by
  rw [← show ((([(71, 1), (489299, 1), (278788001, 1), (15747023677513, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_71, prime_oneHundredTwentyNineDW_489299, prime_oneHundredTwentyNineDW_278788001, prime_oneHundredTwentyNineDW_15747023677513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646478 : Nat.totient 152512428049264093148965646478 = 50428104596957054469845746368 := by
  rw [← show ((([(2, 1), (3, 2), (127, 1), (5557, 1), (12005731112215083381389, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_127, prime_oneHundredTwentyNineDW_5557, prime_oneHundredTwentyNineDW_12005731112215083381389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646479 : Nat.totient 152512428049264093148965646479 = 150006983672488014323001273600 := by
  rw [← show ((([(61, 1), (28711, 1), (9533897, 1), (9133907841129317, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_61, prime_oneHundredTwentyNineDW_28711, prime_oneHundredTwentyNineDW_9533897, prime_oneHundredTwentyNineDW_9133907841129317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646480 : Nat.totient 152512428049264093148965646480 = 59356180544897518360383545856 := by
  rw [← show ((([(2, 4), (5, 1), (37, 1), (7739887, 1), (6657005320046945599, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_37, prime_oneHundredTwentyNineDW_7739887, prime_oneHundredTwentyNineDW_6657005320046945599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646481 : Nat.totient 152512428049264093148965646481 = 79227061420576031115508909440 := by
  rw [← show ((([(3, 1), (7, 1), (11, 1), (455513, 1), (1449414091918837687327, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_455513, prime_oneHundredTwentyNineDW_1449414091918837687327]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646482 : Nat.totient 152512428049264093148965646482 = 72123622530488361188299639296 := by
  rw [← show ((([(2, 1), (19, 1), (607, 1), (798647, 1), (348529057, 1), (23754127963, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_607, prime_oneHundredTwentyNineDW_798647, prime_oneHundredTwentyNineDW_348529057, prime_oneHundredTwentyNineDW_23754127963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646483 : Nat.totient 152512428049264093148965646483 = 151828515815859321430808849640 := by
  rw [← show ((([(223, 1), (683912233404771718156796621, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_223, prime_oneHundredTwentyNineDW_683912233404771718156796621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646484 : Nat.totient 152512428049264093148965646484 = 48560619923417756372996547072 := by
  rw [← show ((([(2, 2), (3, 1), (47, 1), (59, 1), (139, 1), (9343936853, 1), (3528819336877, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_47, prime_oneHundredTwentyNineDW_59, prime_oneHundredTwentyNineDW_139, prime_oneHundredTwentyNineDW_9343936853, prime_oneHundredTwentyNineDW_3528819336877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646485 : Nat.totient 152512428049264093148965646485 = 121390602630074161450547275200 := by
  rw [← show ((([(5, 1), (197, 1), (154834952334278267156310301, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_197, prime_oneHundredTwentyNineDW_154834952334278267156310301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646486 : Nat.totient 152512428049264093148965646486 = 71119281435621719828045070336 := by
  rw [← show ((([(2, 1), (29, 1), (43, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_29, prime_oneHundredTwentyNineDW_43, prime_oneHundredTwentyNineDW_113, prime_oneHundredTwentyNineDW_449, prime_oneHundredTwentyNineDW_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646487 : Nat.totient 152512428049264093148965646487 = 93853801684559602699362474624 := by
  rw [← show ((([(3, 2), (13, 1), (489049577, 1), (2665425117139169443, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_489049577, prime_oneHundredTwentyNineDW_2665425117139169443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646488 : Nat.totient 152512428049264093148965646488 = 61517430187441855575804923904 := by
  rw [← show ((([(2, 3), (7, 1), (17, 1), (327619, 1), (795729673, 1), (614516648287, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_17, prime_oneHundredTwentyNineDW_327619, prime_oneHundredTwentyNineDW_795729673, prime_oneHundredTwentyNineDW_614516648287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646489 : Nat.totient 152512428049264093148965646489 = 152512421285006470280831565600 := by
  rw [← show ((([(22670311, 1), (4149352969, 1), (1621314912071, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_22670311, prime_oneHundredTwentyNineDW_4149352969, prime_oneHundredTwentyNineDW_1621314912071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646490 : Nat.totient 152512428049264093148965646490 = 40456094446671240981369014784 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (199, 1), (4253, 1), (6006694182932220990089, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_199, prime_oneHundredTwentyNineDW_4253, prime_oneHundredTwentyNineDW_6006694182932220990089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646491 : Nat.totient 152512428049264093148965646491 = 152511863987582842353432303240 := by
  rw [← show ((([(314747, 1), (1918243, 1), (252603878142790571, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_314747, prime_oneHundredTwentyNineDW_1918243, prime_oneHundredTwentyNineDW_252603878142790571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646492 : Nat.totient 152512428049264093148965646492 = 69323830931483678704075293840 := by
  rw [← show ((([(2, 2), (11, 1), (3466191546574183935203764693, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_11, prime_oneHundredTwentyNineDW_3466191546574183935203764693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646493 : Nat.totient 152512428049264093148965646493 = 101674951927061432162651906784 := by
  rw [← show ((([(3, 1), (961180807, 1), (52890648300701414633, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_961180807, prime_oneHundredTwentyNineDW_52890648300701414633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646494 : Nat.totient 152512428049264093148965646494 = 75399402631096855039938072336 := by
  rw [← show ((([(2, 1), (89, 1), (856811393535191534544750823, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_89, prime_oneHundredTwentyNineDW_856811393535191534544750823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646495 : Nat.totient 152512428049264093148965646495 = 104525918819943281094220795008 := by
  rw [← show ((([(5, 1), (7, 1), (2003, 1), (57427, 1), (37882629138159203597, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_7, prime_oneHundredTwentyNineDW_2003, prime_oneHundredTwentyNineDW_57427, prime_oneHundredTwentyNineDW_37882629138159203597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646496 : Nat.totient 152512428049264093148965646496 = 46757769010024241916377579520 := by
  rw [← show ((([(2, 5), (3, 4), (23, 1), (31, 2), (157, 1), (50909, 1), (425959, 1), (781910413, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_23, prime_oneHundredTwentyNineDW_31, prime_oneHundredTwentyNineDW_157, prime_oneHundredTwentyNineDW_50909, prime_oneHundredTwentyNineDW_425959, prime_oneHundredTwentyNineDW_781910413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646497 : Nat.totient 152512428049264093148965646497 = 152512428049144429305664426176 := by
  rw [← show ((([(1274520759529, 1), (119662568780460793, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_1274520759529, prime_oneHundredTwentyNineDW_119662568780460793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646498 : Nat.totient 152512428049264093148965646498 = 74732417734135542749035170048 := by
  rw [← show ((([(2, 1), (53, 1), (1093, 1), (4517, 1), (291426551646771307093, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_53, prime_oneHundredTwentyNineDW_1093, prime_oneHundredTwentyNineDW_4517, prime_oneHundredTwentyNineDW_291426551646771307093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646499 : Nat.totient 152512428049264093148965646499 = 101596559530768451024315811840 := by
  rw [← show ((([(3, 1), (1297, 1), (1069936841, 1), (36634128349737929, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_3, prime_oneHundredTwentyNineDW_1297, prime_oneHundredTwentyNineDW_1069936841, prime_oneHundredTwentyNineDW_36634128349737929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646500 : Nat.totient 152512428049264093148965646500 = 56311921243456526137362432000 := by
  rw [← show ((([(2, 2), (5, 3), (13, 1), (156491, 1), (1470404993, 1), (101968385747, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_2, prime_oneHundredTwentyNineDW_5, prime_oneHundredTwentyNineDW_13, prime_oneHundredTwentyNineDW_156491, prime_oneHundredTwentyNineDW_1470404993, prime_oneHundredTwentyNineDW_101968385747]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentyNineDW_152512428049264093148965646501 : Nat.totient 152512428049264093148965646501 = 144054619776477105754775851008 := by
  rw [← show ((([(19, 1), (383, 1), (2689, 1), (7794029730766277381017, 1)] : List FactorBlock).map factorBlockValue).prod) = 152512428049264093148965646501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentyNineDW_19, prime_oneHundredTwentyNineDW_383, prime_oneHundredTwentyNineDW_2689, prime_oneHundredTwentyNineDW_7794029730766277381017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentyNineDW : certifiedKill 1 152512428049264093148965646399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentyNineDW_152512428049264093148965646400, phi_oneHundredTwentyNineDW_152512428049264093148965646401, phi_oneHundredTwentyNineDW_152512428049264093148965646402,
    phi_oneHundredTwentyNineDW_152512428049264093148965646403, phi_oneHundredTwentyNineDW_152512428049264093148965646404, phi_oneHundredTwentyNineDW_152512428049264093148965646405,
    phi_oneHundredTwentyNineDW_152512428049264093148965646406, phi_oneHundredTwentyNineDW_152512428049264093148965646407, phi_oneHundredTwentyNineDW_152512428049264093148965646408,
    phi_oneHundredTwentyNineDW_152512428049264093148965646409, phi_oneHundredTwentyNineDW_152512428049264093148965646410, phi_oneHundredTwentyNineDW_152512428049264093148965646411,
    phi_oneHundredTwentyNineDW_152512428049264093148965646412, phi_oneHundredTwentyNineDW_152512428049264093148965646413, phi_oneHundredTwentyNineDW_152512428049264093148965646414,
    phi_oneHundredTwentyNineDW_152512428049264093148965646415, phi_oneHundredTwentyNineDW_152512428049264093148965646416, phi_oneHundredTwentyNineDW_152512428049264093148965646417,
    phi_oneHundredTwentyNineDW_152512428049264093148965646418, phi_oneHundredTwentyNineDW_152512428049264093148965646419, phi_oneHundredTwentyNineDW_152512428049264093148965646420,
    phi_oneHundredTwentyNineDW_152512428049264093148965646421, phi_oneHundredTwentyNineDW_152512428049264093148965646422, phi_oneHundredTwentyNineDW_152512428049264093148965646423,
    phi_oneHundredTwentyNineDW_152512428049264093148965646424, phi_oneHundredTwentyNineDW_152512428049264093148965646425, phi_oneHundredTwentyNineDW_152512428049264093148965646426,
    phi_oneHundredTwentyNineDW_152512428049264093148965646427, phi_oneHundredTwentyNineDW_152512428049264093148965646428, phi_oneHundredTwentyNineDW_152512428049264093148965646429,
    phi_oneHundredTwentyNineDW_152512428049264093148965646430, phi_oneHundredTwentyNineDW_152512428049264093148965646431, phi_oneHundredTwentyNineDW_152512428049264093148965646432,
    phi_oneHundredTwentyNineDW_152512428049264093148965646433, phi_oneHundredTwentyNineDW_152512428049264093148965646434, phi_oneHundredTwentyNineDW_152512428049264093148965646435,
    phi_oneHundredTwentyNineDW_152512428049264093148965646436, phi_oneHundredTwentyNineDW_152512428049264093148965646437, phi_oneHundredTwentyNineDW_152512428049264093148965646438,
    phi_oneHundredTwentyNineDW_152512428049264093148965646439, phi_oneHundredTwentyNineDW_152512428049264093148965646440, phi_oneHundredTwentyNineDW_152512428049264093148965646441,
    phi_oneHundredTwentyNineDW_152512428049264093148965646442, phi_oneHundredTwentyNineDW_152512428049264093148965646443, phi_oneHundredTwentyNineDW_152512428049264093148965646444,
    phi_oneHundredTwentyNineDW_152512428049264093148965646445, phi_oneHundredTwentyNineDW_152512428049264093148965646446, phi_oneHundredTwentyNineDW_152512428049264093148965646447,
    phi_oneHundredTwentyNineDW_152512428049264093148965646448, phi_oneHundredTwentyNineDW_152512428049264093148965646449, phi_oneHundredTwentyNineDW_152512428049264093148965646450,
    phi_oneHundredTwentyNineDW_152512428049264093148965646451, phi_oneHundredTwentyNineDW_152512428049264093148965646452, phi_oneHundredTwentyNineDW_152512428049264093148965646453,
    phi_oneHundredTwentyNineDW_152512428049264093148965646454, phi_oneHundredTwentyNineDW_152512428049264093148965646455, phi_oneHundredTwentyNineDW_152512428049264093148965646456,
    phi_oneHundredTwentyNineDW_152512428049264093148965646457, phi_oneHundredTwentyNineDW_152512428049264093148965646458, phi_oneHundredTwentyNineDW_152512428049264093148965646459,
    phi_oneHundredTwentyNineDW_152512428049264093148965646460, phi_oneHundredTwentyNineDW_152512428049264093148965646461, phi_oneHundredTwentyNineDW_152512428049264093148965646462,
    phi_oneHundredTwentyNineDW_152512428049264093148965646463, phi_oneHundredTwentyNineDW_152512428049264093148965646464, phi_oneHundredTwentyNineDW_152512428049264093148965646465,
    phi_oneHundredTwentyNineDW_152512428049264093148965646466, phi_oneHundredTwentyNineDW_152512428049264093148965646467, phi_oneHundredTwentyNineDW_152512428049264093148965646468,
    phi_oneHundredTwentyNineDW_152512428049264093148965646469, phi_oneHundredTwentyNineDW_152512428049264093148965646470, phi_oneHundredTwentyNineDW_152512428049264093148965646471,
    phi_oneHundredTwentyNineDW_152512428049264093148965646472, phi_oneHundredTwentyNineDW_152512428049264093148965646473, phi_oneHundredTwentyNineDW_152512428049264093148965646474,
    phi_oneHundredTwentyNineDW_152512428049264093148965646475, phi_oneHundredTwentyNineDW_152512428049264093148965646476, phi_oneHundredTwentyNineDW_152512428049264093148965646477,
    phi_oneHundredTwentyNineDW_152512428049264093148965646478, phi_oneHundredTwentyNineDW_152512428049264093148965646479, phi_oneHundredTwentyNineDW_152512428049264093148965646480,
    phi_oneHundredTwentyNineDW_152512428049264093148965646481, phi_oneHundredTwentyNineDW_152512428049264093148965646482, phi_oneHundredTwentyNineDW_152512428049264093148965646483,
    phi_oneHundredTwentyNineDW_152512428049264093148965646484, phi_oneHundredTwentyNineDW_152512428049264093148965646485, phi_oneHundredTwentyNineDW_152512428049264093148965646486,
    phi_oneHundredTwentyNineDW_152512428049264093148965646487, phi_oneHundredTwentyNineDW_152512428049264093148965646488, phi_oneHundredTwentyNineDW_152512428049264093148965646489,
    phi_oneHundredTwentyNineDW_152512428049264093148965646490, phi_oneHundredTwentyNineDW_152512428049264093148965646491, phi_oneHundredTwentyNineDW_152512428049264093148965646492,
    phi_oneHundredTwentyNineDW_152512428049264093148965646493, phi_oneHundredTwentyNineDW_152512428049264093148965646494, phi_oneHundredTwentyNineDW_152512428049264093148965646495,
    phi_oneHundredTwentyNineDW_152512428049264093148965646496, phi_oneHundredTwentyNineDW_152512428049264093148965646497, phi_oneHundredTwentyNineDW_152512428049264093148965646498,
    phi_oneHundredTwentyNineDW_152512428049264093148965646499, phi_oneHundredTwentyNineDW_152512428049264093148965646500, phi_oneHundredTwentyNineDW_152512428049264093148965646501
    ]

end TotientTailPeriodKiller
end Erdos249257
