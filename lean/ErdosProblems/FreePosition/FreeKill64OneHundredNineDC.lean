import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredNineDCFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredNineDCFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredNineDCFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredNineDCFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredNineDCFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredNineDCFastPow a n * oneHundredNineDCFastPow a n * a else oneHundredNineDCFastPow a n * oneHundredNineDCFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredNineDC_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredNineDC_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredNineDC_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredNineDC_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredNineDC_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredNineDC_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredNineDC_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredNineDC_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredNineDC_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredNineDC_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredNineDC_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredNineDC_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredNineDC_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredNineDC_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredNineDC_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredNineDC_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredNineDC_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredNineDC_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredNineDC_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredNineDC_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredNineDC_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredNineDC_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredNineDC_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredNineDC_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredNineDC_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredNineDC_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredNineDC_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredNineDC_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredNineDC_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredNineDC_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredNineDC_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredNineDC_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredNineDC_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredNineDC_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredNineDC_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredNineDC_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredNineDC_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredNineDC_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredNineDC_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredNineDC_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredNineDC_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredNineDC_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredNineDC_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredNineDC_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredNineDC_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredNineDC_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredNineDC_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredNineDC_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredNineDC_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredNineDC_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredNineDC_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredNineDC_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredNineDC_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredNineDC_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredNineDC_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredNineDC_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredNineDC_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredNineDC_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredNineDC_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredNineDC_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredNineDC_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredNineDC_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredNineDC_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredNineDC_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredNineDC_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredNineDC_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredNineDC_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredNineDC_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredNineDC_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredNineDC_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredNineDC_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredNineDC_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredNineDC_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredNineDC_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredNineDC_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredNineDC_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredNineDC_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredNineDC_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredNineDC_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredNineDC_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredNineDC_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredNineDC_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredNineDC_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredNineDC_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredNineDC_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredNineDC_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredNineDC_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredNineDC_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredNineDC_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredNineDC_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredNineDC_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredNineDC_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredNineDC_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredNineDC_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredNineDC_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredNineDC_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredNineDC_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredNineDC_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredNineDC_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredNineDC_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredNineDC_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredNineDC_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredNineDC_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredNineDC_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredNineDC_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredNineDC_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredNineDC_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredNineDC_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredNineDC_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredNineDC_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredNineDC_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredNineDC_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredNineDC_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredNineDC_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredNineDC_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredNineDC_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredNineDC_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredNineDC_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredNineDC_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredNineDC_1277 : Nat.Prime 1277 := by norm_num

private theorem prime_oneHundredNineDC_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredNineDC_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredNineDC_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredNineDC_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredNineDC_1399 : Nat.Prime 1399 := by norm_num

private theorem prime_oneHundredNineDC_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredNineDC_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredNineDC_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredNineDC_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredNineDC_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredNineDC_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredNineDC_1669 : Nat.Prime 1669 := by norm_num

private theorem prime_oneHundredNineDC_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredNineDC_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredNineDC_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredNineDC_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredNineDC_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredNineDC_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredNineDC_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredNineDC_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredNineDC_1973 : Nat.Prime 1973 := by norm_num

private theorem prime_oneHundredNineDC_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredNineDC_2069 : Nat.Prime 2069 := by norm_num

private theorem prime_oneHundredNineDC_2083 : Nat.Prime 2083 := by norm_num

private theorem prime_oneHundredNineDC_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_oneHundredNineDC_2137 : Nat.Prime 2137 := by norm_num

private theorem prime_oneHundredNineDC_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_oneHundredNineDC_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredNineDC_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredNineDC_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredNineDC_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredNineDC_2657 : Nat.Prime 2657 := by norm_num

private theorem prime_oneHundredNineDC_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredNineDC_2713 : Nat.Prime 2713 := by norm_num

private theorem prime_oneHundredNineDC_2767 : Nat.Prime 2767 := by norm_num

private theorem prime_oneHundredNineDC_2861 : Nat.Prime 2861 := by norm_num

private theorem prime_oneHundredNineDC_2887 : Nat.Prime 2887 := by norm_num

private theorem prime_oneHundredNineDC_2917 : Nat.Prime 2917 := by norm_num

private theorem prime_oneHundredNineDC_3011 : Nat.Prime 3011 := by norm_num

private theorem prime_oneHundredNineDC_3041 : Nat.Prime 3041 := by norm_num

private theorem prime_oneHundredNineDC_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_oneHundredNineDC_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredNineDC_3319 : Nat.Prime 3319 := by norm_num

private theorem prime_oneHundredNineDC_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_oneHundredNineDC_3407 : Nat.Prime 3407 := by norm_num

private theorem prime_oneHundredNineDC_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredNineDC_3851 : Nat.Prime 3851 := by norm_num

private theorem prime_oneHundredNineDC_3877 : Nat.Prime 3877 := by norm_num

private theorem prime_oneHundredNineDC_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredNineDC_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredNineDC_3989 : Nat.Prime 3989 := by norm_num

private theorem prime_oneHundredNineDC_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_oneHundredNineDC_4549 : Nat.Prime 4549 := by norm_num

private theorem prime_oneHundredNineDC_4643 : Nat.Prime 4643 := by norm_num

private theorem prime_oneHundredNineDC_4721 : Nat.Prime 4721 := by norm_num

private theorem prime_oneHundredNineDC_4889 : Nat.Prime 4889 := by norm_num

private theorem prime_oneHundredNineDC_4967 : Nat.Prime 4967 := by norm_num

private theorem prime_oneHundredNineDC_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_oneHundredNineDC_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredNineDC_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_oneHundredNineDC_5227 : Nat.Prime 5227 := by norm_num

private theorem prime_oneHundredNineDC_5479 : Nat.Prime 5479 := by norm_num

private theorem prime_oneHundredNineDC_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredNineDC_5693 : Nat.Prime 5693 := by norm_num

private theorem prime_oneHundredNineDC_6163 : Nat.Prime 6163 := by norm_num

private theorem prime_oneHundredNineDC_6263 : Nat.Prime 6263 := by norm_num

private theorem prime_oneHundredNineDC_6299 : Nat.Prime 6299 := by norm_num

private theorem prime_oneHundredNineDC_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredNineDC_6451 : Nat.Prime 6451 := by norm_num

private theorem prime_oneHundredNineDC_6661 : Nat.Prime 6661 := by norm_num

private theorem prime_oneHundredNineDC_6911 : Nat.Prime 6911 := by norm_num

private theorem prime_oneHundredNineDC_7013 : Nat.Prime 7013 := by norm_num

private theorem prime_oneHundredNineDC_7127 : Nat.Prime 7127 := by norm_num

private theorem prime_oneHundredNineDC_7537 : Nat.Prime 7537 := by norm_num

private theorem prime_oneHundredNineDC_8353 : Nat.Prime 8353 := by norm_num

private theorem prime_oneHundredNineDC_8543 : Nat.Prime 8543 := by norm_num

private theorem prime_oneHundredNineDC_8681 : Nat.Prime 8681 := by norm_num

private theorem prime_oneHundredNineDC_9029 : Nat.Prime 9029 := by norm_num

private theorem prime_oneHundredNineDC_9173 : Nat.Prime 9173 := by norm_num

private theorem prime_oneHundredNineDC_10009 : Nat.Prime 10009 := by norm_num

private theorem prime_oneHundredNineDC_10103 : Nat.Prime 10103 := by norm_num

private theorem prime_oneHundredNineDC_10253 : Nat.Prime 10253 := by norm_num

private theorem prime_oneHundredNineDC_10711 : Nat.Prime 10711 := by norm_num

private theorem prime_oneHundredNineDC_10883 : Nat.Prime 10883 := by norm_num

private theorem prime_oneHundredNineDC_11551 : Nat.Prime 11551 := by norm_num

private theorem prime_oneHundredNineDC_11699 : Nat.Prime 11699 := by norm_num

private theorem prime_oneHundredNineDC_12143 : Nat.Prime 12143 := by norm_num

private theorem prime_oneHundredNineDC_13399 : Nat.Prime 13399 := by norm_num

private theorem prime_oneHundredNineDC_14411 : Nat.Prime 14411 := by norm_num

private theorem prime_oneHundredNineDC_15199 : Nat.Prime 15199 := by norm_num

private theorem prime_oneHundredNineDC_15401 : Nat.Prime 15401 := by norm_num

private theorem prime_oneHundredNineDC_15511 : Nat.Prime 15511 := by norm_num

private theorem prime_oneHundredNineDC_15787 : Nat.Prime 15787 := by norm_num

private theorem prime_oneHundredNineDC_16229 : Nat.Prime 16229 := by norm_num

private theorem prime_oneHundredNineDC_16553 : Nat.Prime 16553 := by norm_num

private theorem prime_oneHundredNineDC_16699 : Nat.Prime 16699 := by norm_num

private theorem prime_oneHundredNineDC_16823 : Nat.Prime 16823 := by norm_num

private theorem prime_oneHundredNineDC_17159 : Nat.Prime 17159 := by norm_num

private theorem prime_oneHundredNineDC_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredNineDC_17417 : Nat.Prime 17417 := by norm_num

private theorem prime_oneHundredNineDC_17729 : Nat.Prime 17729 := by norm_num

private theorem prime_oneHundredNineDC_18211 : Nat.Prime 18211 := by norm_num

private theorem prime_oneHundredNineDC_18493 : Nat.Prime 18493 := by norm_num

private theorem prime_oneHundredNineDC_18541 : Nat.Prime 18541 := by norm_num

private theorem prime_oneHundredNineDC_18637 : Nat.Prime 18637 := by norm_num

private theorem prime_oneHundredNineDC_18743 : Nat.Prime 18743 := by norm_num

private theorem prime_oneHundredNineDC_19051 : Nat.Prime 19051 := by norm_num

private theorem prime_oneHundredNineDC_19319 : Nat.Prime 19319 := by norm_num

private theorem prime_oneHundredNineDC_19421 : Nat.Prime 19421 := by norm_num

private theorem prime_oneHundredNineDC_19919 : Nat.Prime 19919 := by norm_num

private theorem prime_oneHundredNineDC_20011 : Nat.Prime 20011 := by norm_num

private theorem prime_oneHundredNineDC_20477 : Nat.Prime 20477 := by norm_num

private theorem prime_oneHundredNineDC_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredNineDC_21149 : Nat.Prime 21149 := by norm_num

private theorem prime_oneHundredNineDC_21713 : Nat.Prime 21713 := by norm_num

private theorem prime_oneHundredNineDC_21799 : Nat.Prime 21799 := by norm_num

private theorem prime_oneHundredNineDC_22111 : Nat.Prime 22111 := by norm_num

private theorem prime_oneHundredNineDC_25247 : Nat.Prime 25247 := by norm_num

private theorem prime_oneHundredNineDC_25913 : Nat.Prime 25913 := by norm_num

private theorem prime_oneHundredNineDC_26251 : Nat.Prime 26251 := by norm_num

private theorem prime_oneHundredNineDC_26627 : Nat.Prime 26627 := by norm_num

private theorem prime_oneHundredNineDC_27127 : Nat.Prime 27127 := by norm_num

private theorem prime_oneHundredNineDC_27823 : Nat.Prime 27823 := by norm_num

private theorem prime_oneHundredNineDC_28387 : Nat.Prime 28387 := by norm_num

private theorem prime_oneHundredNineDC_30347 : Nat.Prime 30347 := by norm_num

private theorem prime_oneHundredNineDC_31379 : Nat.Prime 31379 := by norm_num

private theorem prime_oneHundredNineDC_32323 : Nat.Prime 32323 := by norm_num

private theorem prime_oneHundredNineDC_33113 : Nat.Prime 33113 := by norm_num

private theorem prime_oneHundredNineDC_34421 : Nat.Prime 34421 := by norm_num

private theorem prime_oneHundredNineDC_35083 : Nat.Prime 35083 := by norm_num

private theorem prime_oneHundredNineDC_36373 : Nat.Prime 36373 := by norm_num

private theorem prime_oneHundredNineDC_37489 : Nat.Prime 37489 := by norm_num

private theorem prime_oneHundredNineDC_37699 : Nat.Prime 37699 := by norm_num

private theorem prime_oneHundredNineDC_39107 : Nat.Prime 39107 := by norm_num

private theorem prime_oneHundredNineDC_40283 : Nat.Prime 40283 := by norm_num

private theorem prime_oneHundredNineDC_40591 : Nat.Prime 40591 := by norm_num

private theorem prime_oneHundredNineDC_41113 : Nat.Prime 41113 := by norm_num

private theorem prime_oneHundredNineDC_42101 : Nat.Prime 42101 := by norm_num

private theorem prime_oneHundredNineDC_42397 : Nat.Prime 42397 := by norm_num

private theorem prime_oneHundredNineDC_42737 : Nat.Prime 42737 := by norm_num

private theorem prime_oneHundredNineDC_42841 : Nat.Prime 42841 := by norm_num

private theorem prime_oneHundredNineDC_44273 : Nat.Prime 44273 := by norm_num

private theorem prime_oneHundredNineDC_45821 : Nat.Prime 45821 := by norm_num

private theorem prime_oneHundredNineDC_47279 : Nat.Prime 47279 := by norm_num

private theorem prime_oneHundredNineDC_47581 : Nat.Prime 47581 := by norm_num

private theorem prime_oneHundredNineDC_48751 : Nat.Prime 48751 := by norm_num

private theorem prime_oneHundredNineDC_49559 : Nat.Prime 49559 := by norm_num

private theorem prime_oneHundredNineDC_50833 : Nat.Prime 50833 := by norm_num

private theorem prime_oneHundredNineDC_51607 : Nat.Prime 51607 := by norm_num

private theorem prime_oneHundredNineDC_52721 : Nat.Prime 52721 := by norm_num

private theorem prime_oneHundredNineDC_52889 : Nat.Prime 52889 := by norm_num

private theorem prime_oneHundredNineDC_55603 : Nat.Prime 55603 := by norm_num

private theorem prime_oneHundredNineDC_55843 : Nat.Prime 55843 := by norm_num

private theorem prime_oneHundredNineDC_56597 : Nat.Prime 56597 := by norm_num

private theorem prime_oneHundredNineDC_57131 : Nat.Prime 57131 := by norm_num

private theorem prime_oneHundredNineDC_57349 : Nat.Prime 57349 := by norm_num

private theorem prime_oneHundredNineDC_59611 : Nat.Prime 59611 := by norm_num

private theorem prime_oneHundredNineDC_61483 : Nat.Prime 61483 := by norm_num

private theorem prime_oneHundredNineDC_62201 : Nat.Prime 62201 := by norm_num

private theorem prime_oneHundredNineDC_63599 : Nat.Prime 63599 := by norm_num

private theorem prime_oneHundredNineDC_63629 : Nat.Prime 63629 := by norm_num

private theorem prime_oneHundredNineDC_64109 : Nat.Prime 64109 := by norm_num

private theorem prime_oneHundredNineDC_72817 : Nat.Prime 72817 := by norm_num

private theorem prime_oneHundredNineDC_77641 : Nat.Prime 77641 := by norm_num

private theorem prime_oneHundredNineDC_77761 : Nat.Prime 77761 := by norm_num

private theorem prime_oneHundredNineDC_78707 : Nat.Prime 78707 := by norm_num

private theorem prime_oneHundredNineDC_85601 : Nat.Prime 85601 := by norm_num

private theorem prime_oneHundredNineDC_97829 : Nat.Prime 97829 := by norm_num

private theorem prime_oneHundredNineDC_98897 : Nat.Prime 98897 := by norm_num

private theorem prime_oneHundredNineDC_99901 : Nat.Prime 99901 := by norm_num

private theorem prime_oneHundredNineDC_101483 : Nat.Prime 101483 := by norm_num

private theorem prime_oneHundredNineDC_105379 : Nat.Prime 105379 := by norm_num

private theorem prime_oneHundredNineDC_108301 : Nat.Prime 108301 := by norm_num

private theorem prime_oneHundredNineDC_111697 : Nat.Prime 111697 := by norm_num

private theorem prime_oneHundredNineDC_116923 : Nat.Prime 116923 := by norm_num

private theorem prime_oneHundredNineDC_121229 : Nat.Prime 121229 := by norm_num

private theorem prime_oneHundredNineDC_122051 : Nat.Prime 122051 := by norm_num

private theorem prime_oneHundredNineDC_127037 : Nat.Prime 127037 := by norm_num

private theorem prime_oneHundredNineDC_137947 : Nat.Prime 137947 := by norm_num

private theorem prime_oneHundredNineDC_152029 : Nat.Prime 152029 := by norm_num

private theorem prime_oneHundredNineDC_153421 : Nat.Prime 153421 := by norm_num

private theorem prime_oneHundredNineDC_157109 : Nat.Prime 157109 := by norm_num

private theorem prime_oneHundredNineDC_161761 : Nat.Prime 161761 := by norm_num

private theorem prime_oneHundredNineDC_167771 : Nat.Prime 167771 := by norm_num

private theorem prime_oneHundredNineDC_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredNineDC_174331 : Nat.Prime 174331 := by norm_num

private theorem prime_oneHundredNineDC_178261 : Nat.Prime 178261 := by norm_num

private theorem prime_oneHundredNineDC_186283 : Nat.Prime 186283 := by norm_num

private theorem prime_oneHundredNineDC_186727 : Nat.Prime 186727 := by norm_num

private theorem prime_oneHundredNineDC_187909 : Nat.Prime 187909 := by norm_num

private theorem prime_oneHundredNineDC_199357 : Nat.Prime 199357 := by norm_num

private theorem prime_oneHundredNineDC_203381 : Nat.Prime 203381 := by norm_num

private theorem prime_oneHundredNineDC_205453 : Nat.Prime 205453 := by norm_num

private theorem prime_oneHundredNineDC_209189 : Nat.Prime 209189 := by norm_num

private theorem prime_oneHundredNineDC_219053 : Nat.Prime 219053 := by norm_num

private theorem prime_oneHundredNineDC_224993 : Nat.Prime 224993 := by norm_num

private theorem prime_oneHundredNineDC_237143 : Nat.Prime 237143 := by norm_num

private theorem prime_oneHundredNineDC_240599 : Nat.Prime 240599 := by norm_num

private theorem prime_oneHundredNineDC_256349 : Nat.Prime 256349 := by norm_num

private theorem prime_oneHundredNineDC_265511 : Nat.Prime 265511 := by norm_num

private theorem prime_oneHundredNineDC_266977 : Nat.Prime 266977 := by norm_num

private theorem prime_oneHundredNineDC_270343 : Nat.Prime 270343 := by norm_num

private theorem prime_oneHundredNineDC_277483 : Nat.Prime 277483 := by norm_num

private theorem prime_oneHundredNineDC_281081 : Nat.Prime 281081 := by norm_num

private theorem prime_oneHundredNineDC_292489 : Nat.Prime 292489 := by norm_num

private theorem prime_oneHundredNineDC_295727 : Nat.Prime 295727 := by norm_num

private theorem prime_oneHundredNineDC_307033 : Nat.Prime 307033 := by norm_num

private theorem prime_oneHundredNineDC_316879 : Nat.Prime 316879 := by norm_num

private theorem prime_oneHundredNineDC_319049 : Nat.Prime 319049 := by norm_num

private theorem prime_oneHundredNineDC_325999 : Nat.Prime 325999 := by norm_num

private theorem prime_oneHundredNineDC_329591 : Nat.Prime 329591 := by norm_num

private theorem prime_oneHundredNineDC_336113 : Nat.Prime 336113 := by norm_num

private theorem prime_oneHundredNineDC_357197 : Nat.Prime 357197 := by norm_num

private theorem prime_oneHundredNineDC_362473 : Nat.Prime 362473 := by norm_num

private theorem prime_oneHundredNineDC_366973 : Nat.Prime 366973 := by norm_num

private theorem prime_oneHundredNineDC_371479 : Nat.Prime 371479 := by norm_num

private theorem prime_oneHundredNineDC_382391 : Nat.Prime 382391 := by norm_num

private theorem prime_oneHundredNineDC_393593 : Nat.Prime 393593 := by norm_num

private theorem prime_oneHundredNineDC_405521 : Nat.Prime 405521 := by norm_num

private theorem prime_oneHundredNineDC_414461 : Nat.Prime 414461 := by norm_num

private theorem prime_oneHundredNineDC_437357 : Nat.Prime 437357 := by norm_num

private theorem prime_oneHundredNineDC_446221 : Nat.Prime 446221 := by norm_num

private theorem prime_oneHundredNineDC_484733 : Nat.Prime 484733 := by norm_num

private theorem prime_oneHundredNineDC_511061 : Nat.Prime 511061 := by norm_num

private theorem prime_oneHundredNineDC_534553 : Nat.Prime 534553 := by norm_num

private theorem prime_oneHundredNineDC_542401 : Nat.Prime 542401 := by norm_num

private theorem prime_oneHundredNineDC_544199 : Nat.Prime 544199 := by norm_num

private theorem prime_oneHundredNineDC_575699 : Nat.Prime 575699 := by norm_num

private theorem prime_oneHundredNineDC_627217 : Nat.Prime 627217 := by norm_num

private theorem prime_oneHundredNineDC_644797 : Nat.Prime 644797 := by norm_num

private theorem prime_oneHundredNineDC_657413 : Nat.Prime 657413 := by norm_num

private theorem prime_oneHundredNineDC_689987 : Nat.Prime 689987 := by norm_num

private theorem prime_oneHundredNineDC_706337 : Nat.Prime 706337 := by norm_num

private theorem prime_oneHundredNineDC_706801 : Nat.Prime 706801 := by norm_num

private theorem prime_oneHundredNineDC_738923 : Nat.Prime 738923 := by norm_num

private theorem prime_oneHundredNineDC_761417 : Nat.Prime 761417 := by norm_num

private theorem prime_oneHundredNineDC_765931 : Nat.Prime 765931 := by norm_num

private theorem prime_oneHundredNineDC_769273 : Nat.Prime 769273 := by norm_num

private theorem prime_oneHundredNineDC_818887 : Nat.Prime 818887 := by norm_num

private theorem prime_oneHundredNineDC_842531 : Nat.Prime 842531 := by norm_num

private theorem prime_oneHundredNineDC_865741 : Nat.Prime 865741 := by norm_num

private theorem prime_oneHundredNineDC_880259 : Nat.Prime 880259 := by norm_num

private theorem prime_oneHundredNineDC_903883 : Nat.Prime 903883 := by norm_num

private theorem prime_oneHundredNineDC_971917 : Nat.Prime 971917 := by norm_num

private theorem prime_oneHundredNineDC_988607 : Nat.Prime 988607 := by norm_num

private theorem prime_oneHundredNineDC_1053713 : Nat.Prime 1053713 := by norm_num

private theorem prime_oneHundredNineDC_1099223 : Nat.Prime 1099223 := by norm_num

private theorem prime_oneHundredNineDC_1156907 : Nat.Prime 1156907 := by norm_num

private theorem prime_oneHundredNineDC_1157729 : Nat.Prime 1157729 := by norm_num

private theorem prime_oneHundredNineDC_1200161 : Nat.Prime 1200161 := by norm_num

private theorem prime_oneHundredNineDC_1204117 : Nat.Prime 1204117 := by norm_num

private theorem prime_oneHundredNineDC_1224577 : Nat.Prime 1224577 := by norm_num

private theorem prime_oneHundredNineDC_1249049 : Nat.Prime 1249049 := by norm_num

private theorem prime_oneHundredNineDC_1402901 : Nat.Prime 1402901 := by norm_num

private theorem prime_oneHundredNineDC_1536811 : Nat.Prime 1536811 := by norm_num

private theorem prime_oneHundredNineDC_1689739 : Nat.Prime 1689739 := by norm_num

private theorem prime_oneHundredNineDC_1718383 : Nat.Prime 1718383 := by norm_num

private theorem prime_oneHundredNineDC_1718713 : Nat.Prime 1718713 := by norm_num

private theorem prime_oneHundredNineDC_1763407 : Nat.Prime 1763407 := by norm_num

private theorem prime_oneHundredNineDC_1776821 : Nat.Prime 1776821 := by norm_num

private theorem prime_oneHundredNineDC_1779619 : Nat.Prime 1779619 := by norm_num

private theorem prime_oneHundredNineDC_1793843 : Nat.Prime 1793843 := by norm_num

private theorem prime_oneHundredNineDC_1905583 : Nat.Prime 1905583 := by norm_num

private theorem prime_oneHundredNineDC_2121569 : Nat.Prime 2121569 := by norm_num

private theorem prime_oneHundredNineDC_2623939 : Nat.Prime 2623939 := by norm_num

private theorem prime_oneHundredNineDC_2823889 : Nat.Prime 2823889 := by norm_num

private theorem prime_oneHundredNineDC_2930633 : Nat.Prime 2930633 := by norm_num

private theorem prime_oneHundredNineDC_3059137 : Nat.Prime 3059137 := by norm_num

private theorem prime_oneHundredNineDC_3146393 : Nat.Prime 3146393 := by norm_num

private theorem prime_oneHundredNineDC_3222269 : Nat.Prime 3222269 := by norm_num

private theorem prime_oneHundredNineDC_3406049 : Nat.Prime 3406049 := by norm_num

private theorem prime_oneHundredNineDC_3445499 : Nat.Prime 3445499 := by norm_num

private theorem prime_oneHundredNineDC_3490703 : Nat.Prime 3490703 := by norm_num

private theorem prime_oneHundredNineDC_3702943 : Nat.Prime 3702943 := by norm_num

private theorem prime_oneHundredNineDC_3830137 : Nat.Prime 3830137 := by norm_num

private theorem prime_oneHundredNineDC_4332443 : Nat.Prime 4332443 := by norm_num

private theorem prime_oneHundredNineDC_4915249 : Nat.Prime 4915249 := by norm_num

private theorem prime_oneHundredNineDC_5050679 : Nat.Prime 5050679 := by norm_num

private theorem prime_oneHundredNineDC_5202157 : Nat.Prime 5202157 := by norm_num

private theorem prime_oneHundredNineDC_5403481 : Nat.Prime 5403481 := by norm_num

private theorem prime_oneHundredNineDC_5466427 : Nat.Prime 5466427 := by norm_num

private theorem prime_oneHundredNineDC_5768957 : Nat.Prime 5768957 := by norm_num

private theorem prime_oneHundredNineDC_5795191 : Nat.Prime 5795191 := by norm_num

private theorem prime_oneHundredNineDC_6075583 : Nat.Prime 6075583 := by norm_num

private theorem prime_oneHundredNineDC_6466133 : Nat.Prime 6466133 := by norm_num

private theorem prime_oneHundredNineDC_6563611 : Nat.Prime 6563611 := by norm_num

private theorem prime_oneHundredNineDC_6604673 : Nat.Prime 6604673 := by norm_num

private theorem prime_oneHundredNineDC_6903341 : Nat.Prime 6903341 := by norm_num

private theorem prime_oneHundredNineDC_6909389 : Nat.Prime 6909389 := by norm_num

private theorem prime_oneHundredNineDC_7682911 : Nat.Prime 7682911 := by norm_num

private theorem prime_oneHundredNineDC_7724257 : Nat.Prime 7724257 := by norm_num

private theorem prime_oneHundredNineDC_8229863 : Nat.Prime 8229863 := by norm_num

private theorem prime_oneHundredNineDC_8867869 : Nat.Prime 8867869 := by norm_num

private theorem prime_oneHundredNineDC_10094881 : Nat.Prime 10094881 := by norm_num

private theorem prime_oneHundredNineDC_10373939 : Nat.Prime 10373939 := by norm_num

private theorem prime_oneHundredNineDC_10453979 : Nat.Prime 10453979 := by norm_num

private theorem prime_oneHundredNineDC_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredNineDC_12485731 : Nat.Prime 12485731 := by norm_num

private theorem prime_oneHundredNineDC_12942607 : Nat.Prime 12942607 := by norm_num

private theorem prime_oneHundredNineDC_13507447 : Nat.Prime 13507447 := by norm_num

private theorem prime_oneHundredNineDC_16294169 : Nat.Prime 16294169 := by norm_num

private theorem prime_oneHundredNineDC_16406867 : Nat.Prime 16406867 := by norm_num

private theorem prime_oneHundredNineDC_17456863 : Nat.Prime 17456863 := by norm_num

private theorem prime_oneHundredNineDC_17596807 : Nat.Prime 17596807 := by norm_num

private theorem prime_oneHundredNineDC_17712361 : Nat.Prime 17712361 := by norm_num

private theorem prime_oneHundredNineDC_18135233 : Nat.Prime 18135233 := by norm_num

private theorem prime_oneHundredNineDC_20763493 : Nat.Prime 20763493 := by norm_num

private theorem prime_oneHundredNineDC_20939981 : Nat.Prime 20939981 := by norm_num

private theorem prime_oneHundredNineDC_23396081 : Nat.Prime 23396081 := by norm_num

private theorem prime_oneHundredNineDC_25076881 : Nat.Prime 25076881 := by norm_num

private theorem prime_oneHundredNineDC_25190353 : Nat.Prime 25190353 := by norm_num

private theorem prime_oneHundredNineDC_25636669 : Nat.Prime 25636669 := by norm_num

private theorem prime_oneHundredNineDC_26802071 : Nat.Prime 26802071 := by norm_num

private theorem prime_oneHundredNineDC_27079891 : Nat.Prime 27079891 := by norm_num

private theorem prime_oneHundredNineDC_30897029 : Nat.Prime 30897029 := by
  apply lucas_primality 30897029 (2 : ZMod 30897029)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7724257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7724257, 1)] : List FactorBlock).map factorBlockValue).prod) = 30897029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7724257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 30897029) ^ 15448514 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30897029) ^ 4 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_32033143 : Nat.Prime 32033143 := by
  apply lucas_primality 32033143 (3 : ZMod 32033143)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (1779619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (1779619, 1)] : List FactorBlock).map factorBlockValue).prod) = 32033143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_1779619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 32033143) ^ 16016571 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 32033143) ^ 10677714 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 32033143) ^ 18 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_33363511 : Nat.Prime 33363511 := by
  apply lucas_primality 33363511 (3 : ZMod 33363511)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (13399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (13399, 1)] : List FactorBlock).map factorBlockValue).prod) = 33363511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_83
      · exact prime_oneHundredNineDC_13399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 33363511) ^ 16681755 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33363511) ^ 11121170 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33363511) ^ 6672702 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33363511) ^ 401970 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 33363511) ^ 2490 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_33632107 : Nat.Prime 33632107 := by
  apply lucas_primality 33632107 (2 : ZMod 33632107)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (61, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (61, 1), (2137, 1)] : List FactorBlock).map factorBlockValue).prod) = 33632107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_61
      · exact prime_oneHundredNineDC_2137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33632107) ^ 16816053 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33632107) ^ 11210702 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33632107) ^ 782142 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33632107) ^ 551346 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 33632107) ^ 15738 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_35709967 : Nat.Prime 35709967 := by
  apply lucas_primality 35709967 (3 : ZMod 35709967)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (18541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (18541, 1)] : List FactorBlock).map factorBlockValue).prod) = 35709967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_107
      · exact prime_oneHundredNineDC_18541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35709967) ^ 17854983 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35709967) ^ 11903322 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35709967) ^ 333738 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 35709967) ^ 1926 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_36182191 : Nat.Prime 36182191 := by
  apply lucas_primality 36182191 (3 : ZMod 36182191)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (83, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (83, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 36182191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_83
      · exact prime_oneHundredNineDC_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36182191) ^ 18091095 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 36182191) ^ 12060730 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 36182191) ^ 7236438 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 36182191) ^ 3289290 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 36182191) ^ 435930 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 36182191) ^ 27390 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_36270467 : Nat.Prime 36270467 := by
  apply lucas_primality 36270467 (2 : ZMod 36270467)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18135233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18135233, 1)] : List FactorBlock).map factorBlockValue).prod) = 36270467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_18135233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 36270467) ^ 18135233 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36270467) ^ 2 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_36737989 : Nat.Prime 36737989 := by
  apply lucas_primality 36737989 (2 : ZMod 36737989)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (437357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (437357, 1)] : List FactorBlock).map factorBlockValue).prod) = 36737989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_437357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36737989) ^ 18368994 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36737989) ^ 12245996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36737989) ^ 5248284 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 36737989) ^ 84 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_37936441 : Nat.Prime 37936441 := by
  apply lucas_primality 37936441 (17 : ZMod 37936441)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (105379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (105379, 1)] : List FactorBlock).map factorBlockValue).prod) = 37936441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_105379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 37936441) ^ 18968220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 37936441) ^ 12645480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 37936441) ^ 7587288 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 37936441) ^ 360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_39373303 : Nat.Prime 39373303 := by
  apply lucas_primality 39373303 (3 : ZMod 39373303)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (127, 1), (163, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (127, 1), (163, 1), (317, 1)] : List FactorBlock).map factorBlockValue).prod) = 39373303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_127
      · exact prime_oneHundredNineDC_163
      · exact prime_oneHundredNineDC_317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39373303) ^ 19686651 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39373303) ^ 13124434 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39373303) ^ 310026 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39373303) ^ 241554 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39373303) ^ 124206 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_42556603 : Nat.Prime 42556603 := by
  apply lucas_primality 42556603 (2 : ZMod 42556603)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (644797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (644797, 1)] : List FactorBlock).map factorBlockValue).prod) = 42556603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_644797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42556603) ^ 21278301 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42556603) ^ 14185534 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42556603) ^ 3868782 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42556603) ^ 66 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_43833347 : Nat.Prime 43833347 := by
  apply lucas_primality 43833347 (2 : ZMod 43833347)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (534553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (534553, 1)] : List FactorBlock).map factorBlockValue).prod) = 43833347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_534553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43833347) ^ 21916673 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 43833347) ^ 1069106 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 43833347) ^ 82 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_44008619 : Nat.Prime 44008619 := by
  apply lucas_primality 44008619 (2 : ZMod 44008619)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (111697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (111697, 1)] : List FactorBlock).map factorBlockValue).prod) = 44008619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_197
      · exact prime_oneHundredNineDC_111697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 44008619) ^ 22004309 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 44008619) ^ 223394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 44008619) ^ 394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_45719459 : Nat.Prime 45719459 := by
  apply lucas_primality 45719459 (2 : ZMod 45719459)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (153421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (153421, 1)] : List FactorBlock).map factorBlockValue).prod) = 45719459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_149
      · exact prime_oneHundredNineDC_153421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45719459) ^ 22859729 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 45719459) ^ 306842 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 45719459) ^ 298 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_46406033 : Nat.Prime 46406033 := by
  apply lucas_primality 46406033 (3 : ZMod 46406033)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (29, 1), (103, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (29, 1), (103, 1), (971, 1)] : List FactorBlock).map factorBlockValue).prod) = 46406033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 46406033) ^ 23203016 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46406033) ^ 1600208 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46406033) ^ 450544 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 46406033) ^ 47792 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_52654079 : Nat.Prime 52654079 := by
  apply lucas_primality 52654079 (7 : ZMod 52654079)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (446221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (446221, 1)] : List FactorBlock).map factorBlockValue).prod) = 52654079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_446221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 52654079) ^ 26327039 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 52654079) ^ 892442 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 52654079) ^ 118 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_53304631 : Nat.Prime 53304631 := by
  apply lucas_primality 53304631 (6 : ZMod 53304631)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1776821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1776821, 1)] : List FactorBlock).map factorBlockValue).prod) = 53304631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_1776821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 53304631) ^ 26652315 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 53304631) ^ 17768210 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 53304631) ^ 10660926 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 53304631) ^ 30 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_60569287 : Nat.Prime 60569287 := by
  apply lucas_primality 60569287 (3 : ZMod 60569287)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (10094881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (10094881, 1)] : List FactorBlock).map factorBlockValue).prod) = 60569287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_10094881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60569287) ^ 30284643 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 60569287) ^ 20189762 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 60569287) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_62974537 : Nat.Prime 62974537 := by
  apply lucas_primality 62974537 (5 : ZMod 62974537)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2623939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2623939, 1)] : List FactorBlock).map factorBlockValue).prod) = 62974537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_2623939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 62974537) ^ 31487268 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62974537) ^ 20991512 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 62974537) ^ 24 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_65901749 : Nat.Prime 65901749 := by
  apply lucas_primality 65901749 (2 : ZMod 65901749)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1063, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1063, 1), (1409, 1)] : List FactorBlock).map factorBlockValue).prod) = 65901749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_1063
      · exact prime_oneHundredNineDC_1409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65901749) ^ 32950874 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 65901749) ^ 5991068 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 65901749) ^ 61996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 65901749) ^ 46772 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_72727861 : Nat.Prime 72727861 := by
  apply lucas_primality 72727861 (2 : ZMod 72727861)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (61, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (61, 1), (641, 1)] : List FactorBlock).map factorBlockValue).prod) = 72727861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_61
      · exact prime_oneHundredNineDC_641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 72727861) ^ 36363930 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72727861) ^ 24242620 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72727861) ^ 14545572 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72727861) ^ 2346060 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72727861) ^ 1192260 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 72727861) ^ 113460 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_76084213 : Nat.Prime 76084213 := by
  apply lucas_primality 76084213 (2 : ZMod 76084213)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1213, 1), (5227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1213, 1), (5227, 1)] : List FactorBlock).map factorBlockValue).prod) = 76084213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_1213
      · exact prime_oneHundredNineDC_5227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76084213) ^ 38042106 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76084213) ^ 25361404 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76084213) ^ 62724 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 76084213) ^ 14556 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_76223321 : Nat.Prime 76223321 := by
  apply lucas_primality 76223321 (3 : ZMod 76223321)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1905583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1905583, 1)] : List FactorBlock).map factorBlockValue).prod) = 76223321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_1905583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 76223321) ^ 38111660 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 76223321) ^ 15244664 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 76223321) ^ 40 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_77626849 : Nat.Prime 77626849 := by
  apply lucas_primality 77626849 (14 : ZMod 77626849)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (62201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (62201, 1)] : List FactorBlock).map factorBlockValue).prod) = 77626849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_62201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 77626849) ^ 38813424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 77626849) ^ 25875616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 77626849) ^ 5971296 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 77626849) ^ 1248 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_77773027 : Nat.Prime 77773027 := by
  apply lucas_primality 77773027 (2 : ZMod 77773027)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109, 2), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109, 2), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 77773027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_109
      · exact prime_oneHundredNineDC_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 77773027) ^ 38886513 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77773027) ^ 25924342 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77773027) ^ 713514 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 77773027) ^ 71286 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_80176391 : Nat.Prime 80176391 := by
  apply lucas_primality 80176391 (7 : ZMod 80176391)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (23, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (23, 1), (2621, 1)] : List FactorBlock).map factorBlockValue).prod) = 80176391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_2621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 80176391) ^ 40088195 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 80176391) ^ 16035278 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 80176391) ^ 11453770 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 80176391) ^ 4219810 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 80176391) ^ 3485930 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 80176391) ^ 30590 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_83042989 : Nat.Prime 83042989 := by
  apply lucas_primality 83042989 (2 : ZMod 83042989)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (988607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (988607, 1)] : List FactorBlock).map factorBlockValue).prod) = 83042989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_988607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 83042989) ^ 41521494 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 83042989) ^ 27680996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 83042989) ^ 11863284 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 83042989) ^ 84 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_88067963 : Nat.Prime 88067963 := by
  apply lucas_primality 88067963 (2 : ZMod 88067963)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 2), (45821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 2), (45821, 1)] : List FactorBlock).map factorBlockValue).prod) = 88067963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_45821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 88067963) ^ 44033981 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 88067963) ^ 2840902 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 88067963) ^ 1922 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_92035963 : Nat.Prime 92035963 := by
  apply lucas_primality 92035963 (2 : ZMod 92035963)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (31, 1), (8681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (31, 1), (8681, 1)] : List FactorBlock).map factorBlockValue).prod) = 92035963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_8681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 92035963) ^ 46017981 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92035963) ^ 30678654 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92035963) ^ 4843998 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92035963) ^ 2968902 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92035963) ^ 10602 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_92334733 : Nat.Prime 92334733 := by
  apply lucas_primality 92334733 (2 : ZMod 92334733)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1099223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1099223, 1)] : List FactorBlock).map factorBlockValue).prod) = 92334733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_1099223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 92334733) ^ 46167366 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92334733) ^ 30778244 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92334733) ^ 13190676 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 92334733) ^ 84 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_95046877 : Nat.Prime 95046877 := by
  apply lucas_primality 95046877 (2 : ZMod 95046877)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (59, 1), (73, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (59, 1), (73, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 95046877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 95046877) ^ 47523438 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 95046877) ^ 31682292 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 95046877) ^ 1610964 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 95046877) ^ 1302012 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 95046877) ^ 155052 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_112546331 : Nat.Prime 112546331 := by
  apply lucas_primality 112546331 (2 : ZMod 112546331)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (865741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (865741, 1)] : List FactorBlock).map factorBlockValue).prod) = 112546331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_865741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 112546331) ^ 56273165 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112546331) ^ 22509266 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112546331) ^ 8657410 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 112546331) ^ 130 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_113101141 : Nat.Prime 113101141 := by
  apply lucas_primality 113101141 (2 : ZMod 113101141)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (79, 1), (107, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (79, 1), (107, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 113101141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_79
      · exact prime_oneHundredNineDC_107
      · exact prime_oneHundredNineDC_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 113101141) ^ 56550570 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 113101141) ^ 37700380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 113101141) ^ 22620228 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 113101141) ^ 1431660 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 113101141) ^ 1057020 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 113101141) ^ 507180 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_119737997 : Nat.Prime 119737997 := by
  apply lucas_primality 119737997 (2 : ZMod 119737997)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (137947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (137947, 1)] : List FactorBlock).map factorBlockValue).prod) = 119737997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_137947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119737997) ^ 59868998 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119737997) ^ 17105428 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119737997) ^ 3862516 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 119737997) ^ 868 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_122954653 : Nat.Prime 122954653 := by
  apply lucas_primality 122954653 (2 : ZMod 122954653)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (79, 1), (14411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (79, 1), (14411, 1)] : List FactorBlock).map factorBlockValue).prod) = 122954653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_79
      · exact prime_oneHundredNineDC_14411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 122954653) ^ 61477326 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 122954653) ^ 40984884 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 122954653) ^ 1556388 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 122954653) ^ 8532 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_125639887 : Nat.Prime 125639887 := by
  apply lucas_primality 125639887 (5 : ZMod 125639887)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (20939981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (20939981, 1)] : List FactorBlock).map factorBlockValue).prod) = 125639887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_20939981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 125639887) ^ 62819943 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 125639887) ^ 41879962 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 125639887) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_126392339 : Nat.Prime 126392339 := by
  apply lucas_primality 126392339 (2 : ZMod 126392339)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (199357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (199357, 1)] : List FactorBlock).map factorBlockValue).prod) = 126392339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_317
      · exact prime_oneHundredNineDC_199357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 126392339) ^ 63196169 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 126392339) ^ 398714 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 126392339) ^ 634 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_142642783 : Nat.Prime 142642783 := by
  apply lucas_primality 142642783 (6 : ZMod 142642783)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (43, 1), (20477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (43, 1), (20477, 1)] : List FactorBlock).map factorBlockValue).prod) = 142642783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_20477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 142642783) ^ 71321391 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 142642783) ^ 47547594 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 142642783) ^ 3317274 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 142642783) ^ 6966 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_162066787 : Nat.Prime 162066787 := by
  apply lucas_primality 162066787 (2 : ZMod 162066787)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (167771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (167771, 1)] : List FactorBlock).map factorBlockValue).prod) = 162066787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_167771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 162066787) ^ 81033393 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 162066787) ^ 54022262 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 162066787) ^ 23152398 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 162066787) ^ 7046382 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 162066787) ^ 966 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_191962543 : Nat.Prime 191962543 := by
  apply lucas_primality 191962543 (3 : ZMod 191962543)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (103, 1), (10711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (103, 1), (10711, 1)] : List FactorBlock).map factorBlockValue).prod) = 191962543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_10711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 191962543) ^ 95981271 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191962543) ^ 63987514 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191962543) ^ 6619398 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191962543) ^ 1863714 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191962543) ^ 17922 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_195530029 : Nat.Prime 195530029 := by
  apply lucas_primality 195530029 (2 : ZMod 195530029)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (16294169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (16294169, 1)] : List FactorBlock).map factorBlockValue).prod) = 195530029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_16294169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 195530029) ^ 97765014 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 195530029) ^ 65176676 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 195530029) ^ 12 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_217205171 : Nat.Prime 217205171 := by
  apply lucas_primality 217205171 (2 : ZMod 217205171)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (37, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (37, 1), (6451, 1)] : List FactorBlock).map factorBlockValue).prod) = 217205171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_6451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217205171) ^ 108602585 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 217205171) ^ 43441034 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 217205171) ^ 31029310 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 217205171) ^ 16708090 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 217205171) ^ 5870410 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 217205171) ^ 33670 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_248837399 : Nat.Prime 248837399 := by
  apply lucas_primality 248837399 (13 : ZMod 248837399)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (97, 1), (197, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (97, 1), (197, 1), (383, 1)] : List FactorBlock).map factorBlockValue).prod) = 248837399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_97
      · exact prime_oneHundredNineDC_197
      · exact prime_oneHundredNineDC_383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 248837399) ^ 124418699 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 248837399) ^ 14637494 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 248837399) ^ 2565334 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 248837399) ^ 1263134 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 248837399) ^ 649706 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_276269347 : Nat.Prime 276269347 := by
  apply lucas_primality 276269347 (2 : ZMod 276269347)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (257, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (257, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 276269347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_257
      · exact prime_oneHundredNineDC_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 276269347) ^ 138134673 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 276269347) ^ 92089782 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 276269347) ^ 16251138 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 276269347) ^ 1074978 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 276269347) ^ 235926 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_307904263 : Nat.Prime 307904263 := by
  apply lucas_primality 307904263 (3 : ZMod 307904263)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (765931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (765931, 1)] : List FactorBlock).map factorBlockValue).prod) = 307904263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_765931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 307904263) ^ 153952131 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 307904263) ^ 102634754 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 307904263) ^ 4595586 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 307904263) ^ 402 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_320893247 : Nat.Prime 320893247 := by
  apply lucas_primality 320893247 (5 : ZMod 320893247)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (331, 1), (484733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (331, 1), (484733, 1)] : List FactorBlock).map factorBlockValue).prod) = 320893247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_331
      · exact prime_oneHundredNineDC_484733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 320893247) ^ 160446623 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 320893247) ^ 969466 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 320893247) ^ 662 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_324074423 : Nat.Prime 324074423 := by
  apply lucas_primality 324074423 (5 : ZMod 324074423)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (409, 1), (56597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (409, 1), (56597, 1)] : List FactorBlock).map factorBlockValue).prod) = 324074423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_409
      · exact prime_oneHundredNineDC_56597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 324074423) ^ 162037211 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 324074423) ^ 46296346 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 324074423) ^ 792358 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 324074423) ^ 5726 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_324903001 : Nat.Prime 324903001 := by
  apply lucas_primality 324903001 (14 : ZMod 324903001)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 3), (108301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 3), (108301, 1)] : List FactorBlock).map factorBlockValue).prod) = 324903001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_108301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 324903001) ^ 162451500 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 324903001) ^ 108301000 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 324903001) ^ 64980600 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 324903001) ^ 3000 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_346943759 : Nat.Prime 346943759 := by
  apply lucas_primality 346943759 (7 : ZMod 346943759)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103, 1), (240599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103, 1), (240599, 1)] : List FactorBlock).map factorBlockValue).prod) = 346943759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_240599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 346943759) ^ 173471879 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 346943759) ^ 49563394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 346943759) ^ 3368386 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 346943759) ^ 1442 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_349488511 : Nat.Prime 349488511 := by
  apply lucas_primality 349488511 (3 : ZMod 349488511)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (40591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (40591, 1)] : List FactorBlock).map factorBlockValue).prod) = 349488511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_40591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 349488511) ^ 174744255 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 349488511) ^ 116496170 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 349488511) ^ 69897702 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 349488511) ^ 49926930 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 349488511) ^ 8524110 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 349488511) ^ 8610 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_376363241 : Nat.Prime 376363241 := by
  apply lucas_primality 376363241 (3 : ZMod 376363241)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (77761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (77761, 1)] : List FactorBlock).map factorBlockValue).prod) = 376363241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_77761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 376363241) ^ 188181620 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 376363241) ^ 75272648 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 376363241) ^ 34214840 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 376363241) ^ 4840 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_434186293 : Nat.Prime 434186293 := by
  apply lucas_primality 434186293 (2 : ZMod 434186293)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (36182191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (36182191, 1)] : List FactorBlock).map factorBlockValue).prod) = 434186293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_36182191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 434186293) ^ 217093146 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 434186293) ^ 144728764 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 434186293) ^ 12 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_448973561 : Nat.Prime 448973561 := by
  apply lucas_primality 448973561 (6 : ZMod 448973561)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (83, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (83, 1), (19319, 1)] : List FactorBlock).map factorBlockValue).prod) = 448973561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_83
      · exact prime_oneHundredNineDC_19319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 448973561) ^ 224486780 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 448973561) ^ 89794712 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 448973561) ^ 64139080 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 448973561) ^ 5409320 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 448973561) ^ 23240 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_502559549 : Nat.Prime 502559549 := by
  apply lucas_primality 502559549 (2 : ZMod 502559549)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (125639887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (125639887, 1)] : List FactorBlock).map factorBlockValue).prod) = 502559549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_125639887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 502559549) ^ 251279774 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 502559549) ^ 4 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_523705891 : Nat.Prime 523705891 := by
  apply lucas_primality 523705891 (2 : ZMod 523705891)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17456863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17456863, 1)] : List FactorBlock).map factorBlockValue).prod) = 523705891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_17456863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 523705891) ^ 261852945 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 523705891) ^ 174568630 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 523705891) ^ 104741178 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 523705891) ^ 30 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_533155723 : Nat.Prime 533155723 := by
  apply lucas_primality 533155723 (2 : ZMod 533155723)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (163, 1), (49559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (163, 1), (49559, 1)] : List FactorBlock).map factorBlockValue).prod) = 533155723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_163
      · exact prime_oneHundredNineDC_49559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 533155723) ^ 266577861 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 533155723) ^ 177718574 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 533155723) ^ 48468702 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 533155723) ^ 3270894 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 533155723) ^ 10758 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_552215779 : Nat.Prime 552215779 := by
  apply lucas_primality 552215779 (2 : ZMod 552215779)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (92035963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (92035963, 1)] : List FactorBlock).map factorBlockValue).prod) = 552215779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_92035963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 552215779) ^ 276107889 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 552215779) ^ 184071926 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 552215779) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_599971529 : Nat.Prime 599971529 := by
  apply lucas_primality 599971529 (3 : ZMod 599971529)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (5768957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (5768957, 1)] : List FactorBlock).map factorBlockValue).prod) = 599971529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_5768957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 599971529) ^ 299985764 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 599971529) ^ 46151656 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 599971529) ^ 104 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_17203
      · exact prime_oneHundredNineDC_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_759013949 : Nat.Prime 759013949 := by
  apply lucas_primality 759013949 (2 : ZMod 759013949)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (139, 1), (17729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (139, 1), (17729, 1)] : List FactorBlock).map factorBlockValue).prod) = 759013949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_139
      · exact prime_oneHundredNineDC_17729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 759013949) ^ 379506974 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 759013949) ^ 108430564 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 759013949) ^ 69001268 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 759013949) ^ 5460532 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 759013949) ^ 42812 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_862674097 : Nat.Prime 862674097 := by
  apply lucas_primality 862674097 (5 : ZMod 862674097)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (47, 1), (382391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (47, 1), (382391, 1)] : List FactorBlock).map factorBlockValue).prod) = 862674097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_47
      · exact prime_oneHundredNineDC_382391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 862674097) ^ 431337048 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 862674097) ^ 287558032 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 862674097) ^ 18354768 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 862674097) ^ 2256 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_962150879 : Nat.Prime 962150879 := by
  apply lucas_primality 962150879 (7 : ZMod 962150879)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (627217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (627217, 1)] : List FactorBlock).map factorBlockValue).prod) = 962150879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_627217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 962150879) ^ 481075439 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 962150879) ^ 74011606 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 962150879) ^ 16307642 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 962150879) ^ 1534 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1065134387 : Nat.Prime 1065134387 := by
  apply lucas_primality 1065134387 (2 : ZMod 1065134387)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1291, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1291, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1065134387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_1291
      · exact prime_oneHundredNineDC_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1065134387) ^ 532567193 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1065134387) ^ 14590882 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1065134387) ^ 825046 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1065134387) ^ 188486 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1201559999 : Nat.Prime 1201559999 := by
  apply lucas_primality 1201559999 (23 : ZMod 1201559999)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (8229863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (8229863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1201559999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_8229863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (23 : ZMod 1201559999) ^ 600779999 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (23 : ZMod 1201559999) ^ 16459726 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (23 : ZMod 1201559999) ^ 146 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1231617053 : Nat.Prime 1231617053 := by
  apply lucas_primality 1231617053 (2 : ZMod 1231617053)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307904263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307904263, 1)] : List FactorBlock).map factorBlockValue).prod) = 1231617053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_307904263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1231617053) ^ 615808526 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1231617053) ^ 4 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1232951483 : Nat.Prime 1232951483 := by
  apply lucas_primality 1232951483 (5 : ZMod 1232951483)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (88067963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (88067963, 1)] : List FactorBlock).map factorBlockValue).prod) = 1232951483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_88067963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1232951483) ^ 616475741 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1232951483) ^ 176135926 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1232951483) ^ 14 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1380352697 : Nat.Prime 1380352697 := by
  apply lucas_primality 1380352697 (3 : ZMod 1380352697)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2713, 1), (63599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2713, 1), (63599, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380352697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_2713
      · exact prime_oneHundredNineDC_63599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1380352697) ^ 690176348 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380352697) ^ 508792 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380352697) ^ 21704 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1380445519 : Nat.Prime 1380445519 := by
  apply lucas_primality 1380445519 (3 : ZMod 1380445519)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (491, 1), (619, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (491, 1), (619, 1), (757, 1)] : List FactorBlock).map factorBlockValue).prod) = 1380445519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_491
      · exact prime_oneHundredNineDC_619
      · exact prime_oneHundredNineDC_757
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1380445519) ^ 690222759 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380445519) ^ 460148506 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380445519) ^ 2811498 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380445519) ^ 2230122 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1380445519) ^ 1823574 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1737641369 : Nat.Prime 1737641369 := by
  apply lucas_primality 1737641369 (3 : ZMod 1737641369)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (217205171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (217205171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1737641369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_217205171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1737641369) ^ 868820684 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1737641369) ^ 8 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1828472629 : Nat.Prime 1828472629 := by
  apply lucas_primality 1828472629 (14 : ZMod 1828472629)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (4915249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (4915249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1828472629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_4915249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 1828472629) ^ 914236314 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1828472629) ^ 609490876 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1828472629) ^ 58982988 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 1828472629) ^ 372 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1925359483 : Nat.Prime 1925359483 := by
  apply lucas_primality 1925359483 (5 : ZMod 1925359483)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (320893247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (320893247, 1)] : List FactorBlock).map factorBlockValue).prod) = 1925359483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_320893247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1925359483) ^ 962679741 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925359483) ^ 641786494 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1925359483) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2022312337 : Nat.Prime 2022312337 := by
  apply lucas_primality 2022312337 (5 : ZMod 2022312337)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (3830137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (3830137, 1)] : List FactorBlock).map factorBlockValue).prod) = 2022312337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_3830137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2022312337) ^ 1011156168 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2022312337) ^ 674104112 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2022312337) ^ 183846576 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2022312337) ^ 528 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2258179447 : Nat.Prime 2258179447 := by
  apply lucas_primality 2258179447 (5 : ZMod 2258179447)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (376363241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (376363241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2258179447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_376363241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2258179447) ^ 1129089723 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2258179447) ^ 752726482 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2258179447) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2333413699 : Nat.Prime 2333413699 := by
  apply lucas_primality 2333413699 (3 : ZMod 2333413699)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (5050679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (5050679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2333413699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_5050679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2333413699) ^ 1166706849 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2333413699) ^ 777804566 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2333413699) ^ 333344814 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2333413699) ^ 212128518 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2333413699) ^ 462 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2399725501 : Nat.Prime 2399725501 := by
  apply lucas_primality 2399725501 (6 : ZMod 2399725501)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (31, 1), (51607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (31, 1), (51607, 1)] : List FactorBlock).map factorBlockValue).prod) = 2399725501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_51607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2399725501) ^ 1199862750 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2399725501) ^ 799908500 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2399725501) ^ 479945100 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2399725501) ^ 77410500 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 2399725501) ^ 46500 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2746894009 : Nat.Prime 2746894009 := by
  apply lucas_primality 2746894009 (7 : ZMod 2746894009)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (43, 1), (71, 1), (37489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (43, 1), (71, 1), (37489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2746894009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_71
      · exact prime_oneHundredNineDC_37489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2746894009) ^ 1373447004 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2746894009) ^ 915631336 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2746894009) ^ 63881256 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2746894009) ^ 38688648 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2746894009) ^ 73272 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2820617083 : Nat.Prime 2820617083 := by
  apply lucas_primality 2820617083 (2 : ZMod 2820617083)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (5403481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (5403481, 1)] : List FactorBlock).map factorBlockValue).prod) = 2820617083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_5403481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2820617083) ^ 1410308541 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2820617083) ^ 940205694 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2820617083) ^ 97262658 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2820617083) ^ 522 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2959071959 : Nat.Prime 2959071959 := by
  apply lucas_primality 2959071959 (7 : ZMod 2959071959)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (25076881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (25076881, 1)] : List FactorBlock).map factorBlockValue).prod) = 2959071959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_25076881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2959071959) ^ 1479535979 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2959071959) ^ 50153762 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 2959071959) ^ 118 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_3376037323 : Nat.Prime 3376037323 := by
  apply lucas_primality 3376037323 (7 : ZMod 3376037323)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (3877, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (3877, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) = 3376037323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_3877
      · exact prime_oneHundredNineDC_6911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3376037323) ^ 1688018661 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3376037323) ^ 1125345774 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3376037323) ^ 482291046 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3376037323) ^ 870786 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 3376037323) ^ 488502 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_3650970331 : Nat.Prime 3650970331 := by
  apply lucas_primality 3650970331 (3 : ZMod 3650970331)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (5795191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (5795191, 1)] : List FactorBlock).map factorBlockValue).prod) = 3650970331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_5795191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3650970331) ^ 1825485165 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3650970331) ^ 1216990110 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3650970331) ^ 730194066 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3650970331) ^ 521567190 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 3650970331) ^ 630 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4301660639 : Nat.Prime 4301660639 := by
  apply lucas_primality 4301660639 (11 : ZMod 4301660639)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (195530029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (195530029, 1)] : List FactorBlock).map factorBlockValue).prod) = 4301660639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_195530029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 4301660639) ^ 2150830319 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4301660639) ^ 391060058 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 4301660639) ^ 22 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4584469451 : Nat.Prime 4584469451 := by
  apply lucas_primality 4584469451 (2 : ZMod 4584469451)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (131, 1), (63629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (131, 1), (63629, 1)] : List FactorBlock).map factorBlockValue).prod) = 4584469451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_131
      · exact prime_oneHundredNineDC_63629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4584469451) ^ 2292234725 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4584469451) ^ 916893890 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4584469451) ^ 416769950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4584469451) ^ 34995950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4584469451) ^ 72050 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4982579341 : Nat.Prime 4982579341 := by
  apply lucas_primality 4982579341 (6 : ZMod 4982579341)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (83042989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (83042989, 1)] : List FactorBlock).map factorBlockValue).prod) = 4982579341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_83042989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4982579341) ^ 2491289670 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4982579341) ^ 1660859780 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4982579341) ^ 996515868 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4982579341) ^ 60 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_5917540903 : Nat.Prime 5917540903 := by
  apply lucas_primality 5917540903 (3 : ZMod 5917540903)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (161761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (67, 1), (161761, 1)] : List FactorBlock).map factorBlockValue).prod) = 5917540903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_161761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5917540903) ^ 2958770451 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917540903) ^ 1972513634 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917540903) ^ 845362986 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917540903) ^ 455195454 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917540903) ^ 88321506 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5917540903) ^ 36582 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6344477989 : Nat.Prime 6344477989 := by
  apply lucas_primality 6344477989 (2 : ZMod 6344477989)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (1156907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (1156907, 1)] : List FactorBlock).map factorBlockValue).prod) = 6344477989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_457
      · exact prime_oneHundredNineDC_1156907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6344477989) ^ 3172238994 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6344477989) ^ 2114825996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6344477989) ^ 13882884 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6344477989) ^ 5484 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6505564771 : Nat.Prime 6505564771 := by
  apply lucas_primality 6505564771 (3 : ZMod 6505564771)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (569, 1), (127037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (569, 1), (127037, 1)] : List FactorBlock).map factorBlockValue).prod) = 6505564771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_569
      · exact prime_oneHundredNineDC_127037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6505564771) ^ 3252782385 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6505564771) ^ 2168521590 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6505564771) ^ 1301112954 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6505564771) ^ 11433330 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6505564771) ^ 51210 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6685844747 : Nat.Prime 6685844747 := by
  apply lucas_primality 6685844747 (2 : ZMod 6685844747)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (20763493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (20763493, 1)] : List FactorBlock).map factorBlockValue).prod) = 6685844747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_20763493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6685844747) ^ 3342922373 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6685844747) ^ 955120678 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6685844747) ^ 290688902 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6685844747) ^ 322 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6796763249 : Nat.Prime 6796763249 := by
  apply lucas_primality 6796763249 (7 : ZMod 6796763249)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (37, 1), (47, 1), (53, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (37, 1), (47, 1), (53, 1), (419, 1)] : List FactorBlock).map factorBlockValue).prod) = 6796763249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_47
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6796763249) ^ 3398381624 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6796763249) ^ 617887568 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6796763249) ^ 183696304 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6796763249) ^ 144611984 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6796763249) ^ 128240816 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6796763249) ^ 16221392 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6895769851 : Nat.Prime 6895769851 := by
  apply lucas_primality 6895769851 (3 : ZMod 6895769851)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (151, 1), (101483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (151, 1), (101483, 1)] : List FactorBlock).map factorBlockValue).prod) = 6895769851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_151
      · exact prime_oneHundredNineDC_101483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6895769851) ^ 3447884925 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6895769851) ^ 2298589950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6895769851) ^ 1379153970 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6895769851) ^ 45667350 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 6895769851) ^ 67950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7547917183 : Nat.Prime 7547917183 := by
  apply lucas_primality 7547917183 (3 : ZMod 7547917183)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (137, 1), (706337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (137, 1), (706337, 1)] : List FactorBlock).map factorBlockValue).prod) = 7547917183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_137
      · exact prime_oneHundredNineDC_706337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7547917183) ^ 3773958591 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7547917183) ^ 2515972394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7547917183) ^ 580609014 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7547917183) ^ 55094286 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7547917183) ^ 10686 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_9401703011 : Nat.Prime 9401703011 := by
  apply lucas_primality 9401703011 (2 : ZMod 9401703011)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (103, 1), (186283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (103, 1), (186283, 1)] : List FactorBlock).map factorBlockValue).prod) = 9401703011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_186283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9401703011) ^ 4700851505 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9401703011) ^ 1880340602 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9401703011) ^ 1343100430 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9401703011) ^ 91278670 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 9401703011) ^ 50470 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_11966810789 : Nat.Prime 11966810789 := by
  apply lucas_primality 11966810789 (2 : ZMod 11966810789)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3889, 1), (769273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3889, 1), (769273, 1)] : List FactorBlock).map factorBlockValue).prod) = 11966810789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3889
      · exact prime_oneHundredNineDC_769273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11966810789) ^ 5983405394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966810789) ^ 3077092 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11966810789) ^ 15556 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_11999430581 : Nat.Prime 11999430581 := by
  apply lucas_primality 11999430581 (2 : ZMod 11999430581)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (599971529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (599971529, 1)] : List FactorBlock).map factorBlockValue).prod) = 11999430581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_599971529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11999430581) ^ 5999715290 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11999430581) ^ 2399886116 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 11999430581) ^ 20 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_17328801949 : Nat.Prime 17328801949 := by
  apply lucas_primality 17328801949 (2 : ZMod 17328801949)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (367, 1), (1889, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (367, 1), (1889, 1), (2083, 1)] : List FactorBlock).map factorBlockValue).prod) = 17328801949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_367
      · exact prime_oneHundredNineDC_1889
      · exact prime_oneHundredNineDC_2083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17328801949) ^ 8664400974 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17328801949) ^ 5776267316 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17328801949) ^ 47217444 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17328801949) ^ 9173532 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 17328801949) ^ 8319156 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_18578767729 : Nat.Prime 18578767729 := by
  apply lucas_primality 18578767729 (13 : ZMod 18578767729)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (12485731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (12485731, 1)] : List FactorBlock).map factorBlockValue).prod) = 18578767729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_12485731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 18578767729) ^ 9289383864 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 18578767729) ^ 6192922576 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 18578767729) ^ 599315088 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 18578767729) ^ 1488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_21531233981 : Nat.Prime 21531233981 := by
  apply lucas_primality 21531233981 (2 : ZMod 21531233981)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (163, 1), (6604673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (163, 1), (6604673, 1)] : List FactorBlock).map factorBlockValue).prod) = 21531233981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_163
      · exact prime_oneHundredNineDC_6604673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21531233981) ^ 10765616990 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21531233981) ^ 4306246796 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21531233981) ^ 132093460 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 21531233981) ^ 3260 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_22176557077 : Nat.Prime 22176557077 := by
  apply lucas_primality 22176557077 (2 : ZMod 22176557077)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41, 1), (61, 1), (738923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41, 1), (61, 1), (738923, 1)] : List FactorBlock).map factorBlockValue).prod) = 22176557077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_61
      · exact prime_oneHundredNineDC_738923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22176557077) ^ 11088278538 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22176557077) ^ 7392185692 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22176557077) ^ 540891636 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22176557077) ^ 363550116 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 22176557077) ^ 30012 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_24831333557 : Nat.Prime 24831333557 := by
  apply lucas_primality 24831333557 (2 : ZMod 24831333557)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1973, 1), (3146393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1973, 1), (3146393, 1)] : List FactorBlock).map factorBlockValue).prod) = 24831333557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_1973
      · exact prime_oneHundredNineDC_3146393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 24831333557) ^ 12415666778 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 24831333557) ^ 12585572 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 24831333557) ^ 7892 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_26715641263 : Nat.Prime 26715641263 := by
  apply lucas_primality 26715641263 (6 : ZMod 26715641263)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (32033143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (32033143, 1)] : List FactorBlock).map factorBlockValue).prod) = 26715641263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_139
      · exact prime_oneHundredNineDC_32033143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 26715641263) ^ 13357820631 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26715641263) ^ 8905213754 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26715641263) ^ 192198858 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 26715641263) ^ 834 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_27445910671 : Nat.Prime 27445910671 := by
  apply lucas_primality 27445910671 (6 : ZMod 27445910671)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (277, 1), (366973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (277, 1), (366973, 1)] : List FactorBlock).map factorBlockValue).prod) = 27445910671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_277
      · exact prime_oneHundredNineDC_366973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 27445910671) ^ 13722955335 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 27445910671) ^ 9148636890 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 27445910671) ^ 5489182134 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 27445910671) ^ 99082710 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 27445910671) ^ 74790 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_30152573597 : Nat.Prime 30152573597 := by
  apply lucas_primality 30152573597 (2 : ZMod 30152573597)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1091, 1), (6909389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1091, 1), (6909389, 1)] : List FactorBlock).map factorBlockValue).prod) = 30152573597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_1091
      · exact prime_oneHundredNineDC_6909389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30152573597) ^ 15076286798 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30152573597) ^ 27637556 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30152573597) ^ 4364 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_34768398953 : Nat.Prime 34768398953 := by
  apply lucas_primality 34768398953 (3 : ZMod 34768398953)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (89, 1), (641, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (89, 1), (641, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) = 34768398953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_89
      · exact prime_oneHundredNineDC_641
      · exact prime_oneHundredNineDC_10883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34768398953) ^ 17384199476 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 34768398953) ^ 4966914136 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 34768398953) ^ 390656168 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 34768398953) ^ 54240872 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 34768398953) ^ 3194744 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_38953660631 : Nat.Prime 38953660631 := by
  apply lucas_primality 38953660631 (7 : ZMod 38953660631)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 2), (1763407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 2), (1763407, 1)] : List FactorBlock).map factorBlockValue).prod) = 38953660631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_47
      · exact prime_oneHundredNineDC_1763407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 38953660631) ^ 19476830315 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 38953660631) ^ 7790732126 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 38953660631) ^ 828801290 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 38953660631) ^ 22090 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_68666021777 : Nat.Prime 68666021777 := by
  apply lucas_primality 68666021777 (3 : ZMod 68666021777)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (227, 1), (1718713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (227, 1), (1718713, 1)] : List FactorBlock).map factorBlockValue).prod) = 68666021777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_227
      · exact prime_oneHundredNineDC_1718713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 68666021777) ^ 34333010888 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 68666021777) ^ 6242365616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 68666021777) ^ 302493488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 68666021777) ^ 39952 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_73377602651 : Nat.Prime 73377602651 := by
  apply lucas_primality 73377602651 (6 : ZMod 73377602651)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (11, 1), (23, 1), (37, 1), (211, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (11, 1), (23, 1), (37, 1), (211, 1), (743, 1)] : List FactorBlock).map factorBlockValue).prod) = 73377602651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_211
      · exact prime_oneHundredNineDC_743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 73377602651) ^ 36688801325 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 14675520530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 6670691150 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 3190330550 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 1983178450 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 347761150 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 73377602651) ^ 98758550 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_78066777253 : Nat.Prime 78066777253 := by
  apply lucas_primality 78066777253 (5 : ZMod 78066777253)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6505564771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6505564771, 1)] : List FactorBlock).map factorBlockValue).prod) = 78066777253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_6505564771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 78066777253) ^ 39033388626 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 78066777253) ^ 26022259084 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 78066777253) ^ 12 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_87453113191 : Nat.Prime 87453113191 := by
  apply lucas_primality 87453113191 (3 : ZMod 87453113191)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (151, 1), (269, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (151, 1), (269, 1), (1669, 1)] : List FactorBlock).map factorBlockValue).prod) = 87453113191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_151
      · exact prime_oneHundredNineDC_269
      · exact prime_oneHundredNineDC_1669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 87453113191) ^ 43726556595 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 29151037730 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 17490622638 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 2033793330 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 579159690 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 325104510 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 87453113191) ^ 52398510 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_90081260471 : Nat.Prime 90081260471 := by
  apply lucas_primality 90081260471 (11 : ZMod 90081260471)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (16553, 1), (544199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (16553, 1), (544199, 1)] : List FactorBlock).map factorBlockValue).prod) = 90081260471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_16553
      · exact prime_oneHundredNineDC_544199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 90081260471) ^ 45040630235 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 90081260471) ^ 18016252094 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 90081260471) ^ 5441990 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 90081260471) ^ 165530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_103516510681 : Nat.Prime 103516510681 := by
  apply lucas_primality 103516510681 (7 : ZMod 103516510681)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (11, 1), (31, 1), (281081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (11, 1), (31, 1), (281081, 1)] : List FactorBlock).map factorBlockValue).prod) = 103516510681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_281081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 103516510681) ^ 51758255340 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 103516510681) ^ 34505503560 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 103516510681) ^ 20703302136 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 103516510681) ^ 9410591880 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 103516510681) ^ 3339242280 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 103516510681) ^ 368280 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_110998284707 : Nat.Prime 110998284707 := by
  apply lucas_primality 110998284707 (2 : ZMod 110998284707)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (419, 1), (6263, 1), (21149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (419, 1), (6263, 1), (21149, 1)] : List FactorBlock).map factorBlockValue).prod) = 110998284707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_419
      · exact prime_oneHundredNineDC_6263
      · exact prime_oneHundredNineDC_21149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110998284707) ^ 55499142353 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 110998284707) ^ 264912374 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 110998284707) ^ 17722862 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 110998284707) ^ 5248394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_111139529687 : Nat.Prime 111139529687 := by
  apply lucas_primality 111139529687 (5 : ZMod 111139529687)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (187909, 1), (295727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (187909, 1), (295727, 1)] : List FactorBlock).map factorBlockValue).prod) = 111139529687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_187909
      · exact prime_oneHundredNineDC_295727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 111139529687) ^ 55569764843 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 111139529687) ^ 591454 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 111139529687) ^ 375818 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_129376209367 : Nat.Prime 129376209367 := by
  apply lucas_primality 129376209367 (5 : ZMod 129376209367)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (10103, 1), (237143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (10103, 1), (237143, 1)] : List FactorBlock).map factorBlockValue).prod) = 129376209367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_10103
      · exact prime_oneHundredNineDC_237143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 129376209367) ^ 64688104683 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 129376209367) ^ 43125403122 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 129376209367) ^ 12805722 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 129376209367) ^ 545562 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_159500557991 : Nat.Prime 159500557991 := by
  apply lucas_primality 159500557991 (11 : ZMod 159500557991)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (31, 1), (27079891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (31, 1), (27079891, 1)] : List FactorBlock).map factorBlockValue).prod) = 159500557991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_27079891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 159500557991) ^ 79750278995 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 159500557991) ^ 31900111598 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 159500557991) ^ 8394766210 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 159500557991) ^ 5145179290 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 159500557991) ^ 5890 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_179049774539 : Nat.Prime 179049774539 := by
  apply lucas_primality 179049774539 (2 : ZMod 179049774539)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (109, 1), (35709967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (109, 1), (35709967, 1)] : List FactorBlock).map factorBlockValue).prod) = 179049774539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_109
      · exact prime_oneHundredNineDC_35709967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 179049774539) ^ 89524887269 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179049774539) ^ 7784772806 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179049774539) ^ 1642658482 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 179049774539) ^ 5014 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_191819535137 : Nat.Prime 191819535137 := by
  apply lucas_primality 191819535137 (3 : ZMod 191819535137)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (53, 1), (113101141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (53, 1), (113101141, 1)] : List FactorBlock).map factorBlockValue).prod) = 191819535137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_113101141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 191819535137) ^ 95909767568 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191819535137) ^ 3619236512 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 191819535137) ^ 1696 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_206302253419 : Nat.Prime 206302253419 := by
  apply lucas_primality 206302253419 (2 : ZMod 206302253419)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (73, 1), (149, 1), (1053713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (73, 1), (149, 1), (1053713, 1)] : List FactorBlock).map factorBlockValue).prod) = 206302253419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_149
      · exact prime_oneHundredNineDC_1053713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 206302253419) ^ 103151126709 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 206302253419) ^ 68767417806 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 206302253419) ^ 2826058266 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 206302253419) ^ 1384578882 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 206302253419) ^ 195786 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_273988121101 : Nat.Prime 273988121101 := by
  apply lucas_primality 273988121101 (2 : ZMod 273988121101)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (17, 1), (41, 1), (83, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (17, 1), (41, 1), (83, 1), (15787, 1)] : List FactorBlock).map factorBlockValue).prod) = 273988121101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_83
      · exact prime_oneHundredNineDC_15787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 273988121101) ^ 136994060550 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 91329373700 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 54797624220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 16116948300 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 6682637100 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 3301061700 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273988121101) ^ 17355300 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_306078860959 : Nat.Prime 306078860959 := by
  apply lucas_primality 306078860959 (3 : ZMod 306078860959)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (223, 1), (17596807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (223, 1), (17596807, 1)] : List FactorBlock).map factorBlockValue).prod) = 306078860959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_223
      · exact prime_oneHundredNineDC_17596807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 306078860959) ^ 153039430479 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 306078860959) ^ 102026286986 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 306078860959) ^ 23544527766 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 306078860959) ^ 1372550946 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 306078860959) ^ 17394 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_319540316101 : Nat.Prime 319540316101 := by
  apply lucas_primality 319540316101 (6 : ZMod 319540316101)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (1065134387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (1065134387, 1)] : List FactorBlock).map factorBlockValue).prod) = 319540316101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_1065134387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 319540316101) ^ 159770158050 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 319540316101) ^ 106513438700 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 319540316101) ^ 63908063220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 319540316101) ^ 300 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_358099549079 : Nat.Prime 358099549079 := by
  apply lucas_primality 358099549079 (17 : ZMod 358099549079)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (179049774539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (179049774539, 1)] : List FactorBlock).map factorBlockValue).prod) = 358099549079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_179049774539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (17 : ZMod 358099549079) ^ 179049774539 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 358099549079) ^ 2 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_558612553841 : Nat.Prime 558612553841 := by
  apply lucas_primality 558612553841 (3 : ZMod 558612553841)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (197, 1), (3222269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (197, 1), (3222269, 1)] : List FactorBlock).map factorBlockValue).prod) = 558612553841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_197
      · exact prime_oneHundredNineDC_3222269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 558612553841) ^ 279306276920 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 558612553841) ^ 111722510768 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 558612553841) ^ 50782959440 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 558612553841) ^ 2835596720 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 558612553841) ^ 173360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_613122649781 : Nat.Prime 613122649781 := by
  apply lucas_primality 613122649781 (3 : ZMod 613122649781)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (502559549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (502559549, 1)] : List FactorBlock).map factorBlockValue).prod) = 613122649781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_61
      · exact prime_oneHundredNineDC_502559549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 613122649781) ^ 306561324890 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 613122649781) ^ 122624529956 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 613122649781) ^ 10051190980 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 613122649781) ^ 1220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_652048621373 : Nat.Prime 652048621373 := by
  apply lucas_primality 652048621373 (2 : ZMod 652048621373)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (331, 1), (409, 1), (1204117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (331, 1), (409, 1), (1204117, 1)] : List FactorBlock).map factorBlockValue).prod) = 652048621373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_331
      · exact prime_oneHundredNineDC_409
      · exact prime_oneHundredNineDC_1204117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 652048621373) ^ 326024310686 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 652048621373) ^ 1969935412 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 652048621373) ^ 1594250908 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 652048621373) ^ 541516 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_760858730461 : Nat.Prime 760858730461 := by
  apply lucas_primality 760858730461 (10 : ZMod 760858730461)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (19, 1), (577, 1), (42841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (19, 1), (577, 1), (42841, 1)] : List FactorBlock).map factorBlockValue).prod) = 760858730461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_577
      · exact prime_oneHundredNineDC_42841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 760858730461) ^ 380429365230 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 760858730461) ^ 253619576820 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 760858730461) ^ 152171746092 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 760858730461) ^ 40045196340 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 760858730461) ^ 1318645980 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 760858730461) ^ 17760060 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_874531131911 : Nat.Prime 874531131911 := by
  apply lucas_primality 874531131911 (13 : ZMod 874531131911)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (87453113191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (87453113191, 1)] : List FactorBlock).map factorBlockValue).prod) = 874531131911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_87453113191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 874531131911) ^ 437265565955 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 874531131911) ^ 174906226382 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 874531131911) ^ 10 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_877963924249 : Nat.Prime 877963924249 := by
  apply lucas_primality 877963924249 (7 : ZMod 877963924249)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (1925359483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (1925359483, 1)] : List FactorBlock).map factorBlockValue).prod) = 877963924249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_1925359483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 877963924249) ^ 438981962124 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 877963924249) ^ 292654641416 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 877963924249) ^ 46208627592 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 877963924249) ^ 456 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1150917210823 : Nat.Prime 1150917210823 := by
  apply lucas_primality 1150917210823 (7 : ZMod 1150917210823)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191819535137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191819535137, 1)] : List FactorBlock).map factorBlockValue).prod) = 1150917210823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_191819535137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1150917210823) ^ 575458605411 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1150917210823) ^ 383639070274 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1150917210823) ^ 6 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1270537675189 : Nat.Prime 1270537675189 := by
  apply lucas_primality 1270537675189 (2 : ZMod 1270537675189)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (3650970331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (3650970331, 1)] : List FactorBlock).map factorBlockValue).prod) = 1270537675189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_3650970331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1270537675189) ^ 635268837594 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270537675189) ^ 423512558396 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270537675189) ^ 43811643972 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270537675189) ^ 348 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1426862956439 : Nat.Prime 1426862956439 := by
  apply lucas_primality 1426862956439 (7 : ZMod 1426862956439)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (827, 1), (862674097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (827, 1), (862674097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1426862956439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_827
      · exact prime_oneHundredNineDC_862674097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1426862956439) ^ 713431478219 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1426862956439) ^ 1725348194 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1426862956439) ^ 1654 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1513525326679 : Nat.Prime 1513525326679 := by
  apply lucas_primality 1513525326679 (6 : ZMod 1513525326679)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (919, 1), (1033, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (919, 1), (1033, 1), (3851, 1)] : List FactorBlock).map factorBlockValue).prod) = 1513525326679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_919
      · exact prime_oneHundredNineDC_1033
      · exact prime_oneHundredNineDC_3851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1513525326679) ^ 756762663339 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1513525326679) ^ 504508442226 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1513525326679) ^ 65805448986 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1513525326679) ^ 1646926362 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1513525326679) ^ 1465174566 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1513525326679) ^ 393021378 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1546556444249 : Nat.Prime 1546556444249 := by
  apply lucas_primality 1546556444249 (6 : ZMod 1546556444249)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (43, 1), (463, 1), (511061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (43, 1), (463, 1), (511061, 1)] : List FactorBlock).map factorBlockValue).prod) = 1546556444249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_463
      · exact prime_oneHundredNineDC_511061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1546556444249) ^ 773278222124 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1546556444249) ^ 81397707592 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1546556444249) ^ 35966428936 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1546556444249) ^ 3340294696 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 1546556444249) ^ 3026168 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1579920046879 : Nat.Prime 1579920046879 := by
  apply lucas_primality 1579920046879 (3 : ZMod 1579920046879)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (181, 1), (811, 1), (1793843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (181, 1), (811, 1), (1793843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1579920046879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_181
      · exact prime_oneHundredNineDC_811
      · exact prime_oneHundredNineDC_1793843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1579920046879) ^ 789960023439 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579920046879) ^ 526640015626 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579920046879) ^ 8728840038 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579920046879) ^ 1948113498 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1579920046879) ^ 880746 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1708433116711 : Nat.Prime 1708433116711 := by
  apply lucas_primality 1708433116711 (3 : ZMod 1708433116711)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (157109, 1), (362473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (157109, 1), (362473, 1)] : List FactorBlock).map factorBlockValue).prod) = 1708433116711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_157109
      · exact prime_oneHundredNineDC_362473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1708433116711) ^ 854216558355 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708433116711) ^ 569477705570 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708433116711) ^ 341686623342 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708433116711) ^ 10874190 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1708433116711) ^ 4713270 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1767962121901 : Nat.Prime 1767962121901 := by
  apply lucas_primality 1767962121901 (7 : ZMod 1767962121901)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (29, 1), (911, 1), (17159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (29, 1), (911, 1), (17159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1767962121901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_911
      · exact prime_oneHundredNineDC_17159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1767962121901) ^ 883981060950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 589320707300 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 353592424380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 135997086300 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 60964211100 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 1940682900 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 1767962121901) ^ 103034100 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2255708169053 : Nat.Prime 2255708169053 := by
  apply lucas_primality 2255708169053 (2 : ZMod 2255708169053)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (283, 1), (5051, 1), (30347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (283, 1), (5051, 1), (30347, 1)] : List FactorBlock).map factorBlockValue).prod) = 2255708169053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_283
      · exact prime_oneHundredNineDC_5051
      · exact prime_oneHundredNineDC_30347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2255708169053) ^ 1127854084526 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2255708169053) ^ 173516013004 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2255708169053) ^ 7970700244 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2255708169053) ^ 446586452 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2255708169053) ^ 74330516 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2392536866659 : Nat.Prime 2392536866659 := by
  apply lucas_primality 2392536866659 (3 : ZMod 2392536866659)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1733, 1), (2687, 1), (4507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1733, 1), (2687, 1), (4507, 1)] : List FactorBlock).map factorBlockValue).prod) = 2392536866659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_1733
      · exact prime_oneHundredNineDC_2687
      · exact prime_oneHundredNineDC_4507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2392536866659) ^ 1196268433329 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392536866659) ^ 797512288886 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392536866659) ^ 125922992982 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392536866659) ^ 1380575226 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392536866659) ^ 890411934 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2392536866659) ^ 530849094 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2891992351361 : Nat.Prime 2891992351361 := by
  apply lucas_primality 2891992351361 (3 : ZMod 2891992351361)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (7, 1), (149, 1), (4332443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (7, 1), (149, 1), (4332443, 1)] : List FactorBlock).map factorBlockValue).prod) = 2891992351361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_149
      · exact prime_oneHundredNineDC_4332443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2891992351361) ^ 1445996175680 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2891992351361) ^ 578398470272 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2891992351361) ^ 413141764480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2891992351361) ^ 19409344640 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 2891992351361) ^ 667520 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_3511855696997 : Nat.Prime 3511855696997 := by
  apply lucas_primality 3511855696997 (2 : ZMod 3511855696997)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (877963924249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (877963924249, 1)] : List FactorBlock).map factorBlockValue).prod) = 3511855696997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_877963924249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3511855696997) ^ 1755927848498 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3511855696997) ^ 4 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4221133616423 : Nat.Prime 4221133616423 := by
  apply lucas_primality 4221133616423 (5 : ZMod 4221133616423)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1249049, 1), (1689739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1249049, 1), (1689739, 1)] : List FactorBlock).map factorBlockValue).prod) = 4221133616423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_1249049
      · exact prime_oneHundredNineDC_1689739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 4221133616423) ^ 2110566808211 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4221133616423) ^ 3379478 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 4221133616423) ^ 2498098 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4653663715189 : Nat.Prime 4653663715189 := by
  apply lucas_primality 4653663715189 (6 : ZMod 4653663715189)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1973, 1), (2027, 1), (32323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1973, 1), (2027, 1), (32323, 1)] : List FactorBlock).map factorBlockValue).prod) = 4653663715189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_1973
      · exact prime_oneHundredNineDC_2027
      · exact prime_oneHundredNineDC_32323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4653663715189) ^ 2326831857594 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4653663715189) ^ 1551221238396 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4653663715189) ^ 2358673956 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4653663715189) ^ 2295838044 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 4653663715189) ^ 143973756 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6319680187517 : Nat.Prime 6319680187517 := by
  apply lucas_primality 6319680187517 (2 : ZMod 6319680187517)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1579920046879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1579920046879, 1)] : List FactorBlock).map factorBlockValue).prod) = 6319680187517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_1579920046879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 6319680187517) ^ 3159840093758 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 6319680187517) ^ 4 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_6688356382441 : Nat.Prime 6688356382441 := by
  apply lucas_primality 6688356382441 (7 : ZMod 6688356382441)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (18578767729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (18578767729, 1)] : List FactorBlock).map factorBlockValue).prod) = 6688356382441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_18578767729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 6688356382441) ^ 3344178191220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6688356382441) ^ 2229452127480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6688356382441) ^ 1337671276488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 6688356382441) ^ 360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7382457017569 : Nat.Prime 7382457017569 := by
  apply lucas_primality 7382457017569 (11 : ZMod 7382457017569)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (17, 1), (1277, 1), (393593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (17, 1), (1277, 1), (393593, 1)] : List FactorBlock).map factorBlockValue).prod) = 7382457017569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_1277
      · exact prime_oneHundredNineDC_393593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7382457017569) ^ 3691228508784 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 7382457017569) ^ 2460819005856 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 7382457017569) ^ 434262177504 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 7382457017569) ^ 5781093984 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 7382457017569) ^ 18756576 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7461052515971 : Nat.Prime 7461052515971 := by
  apply lucas_primality 7461052515971 (2 : ZMod 7461052515971)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (219053, 1), (3406049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (219053, 1), (3406049, 1)] : List FactorBlock).map factorBlockValue).prod) = 7461052515971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_219053
      · exact prime_oneHundredNineDC_3406049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7461052515971) ^ 3730526257985 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7461052515971) ^ 1492210503194 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7461052515971) ^ 34060490 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7461052515971) ^ 2190530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_8397421002233 : Nat.Prime 8397421002233 := by
  apply lucas_primality 8397421002233 (3 : ZMod 8397421002233)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (157, 1), (6685844747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (157, 1), (6685844747, 1)] : List FactorBlock).map factorBlockValue).prod) = 8397421002233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_157
      · exact prime_oneHundredNineDC_6685844747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8397421002233) ^ 4198710501116 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8397421002233) ^ 53486757976 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8397421002233) ^ 1256 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_9662586588223 : Nat.Prime 9662586588223 := by
  apply lucas_primality 9662586588223 (3 : ZMod 9662586588223)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (103, 1), (1399, 1), (657413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (103, 1), (1399, 1), (657413, 1)] : List FactorBlock).map factorBlockValue).prod) = 9662586588223 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_1399
      · exact prime_oneHundredNineDC_657413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9662586588223) ^ 4831293294111 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9662586588223) ^ 3220862196074 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9662586588223) ^ 568387446366 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9662586588223) ^ 93811520274 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9662586588223) ^ 6906780978 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9662586588223) ^ 14697894 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_11481253018303 : Nat.Prime 11481253018303 := by
  apply lucas_primality 11481253018303 (3 : ZMod 11481253018303)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (41, 1), (15401, 1), (178261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (41, 1), (15401, 1), (178261, 1)] : List FactorBlock).map factorBlockValue).prod) = 11481253018303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_15401
      · exact prime_oneHundredNineDC_178261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11481253018303) ^ 5740626509151 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11481253018303) ^ 3827084339434 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11481253018303) ^ 675367824606 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11481253018303) ^ 280030561422 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11481253018303) ^ 745487502 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 11481253018303) ^ 64406982 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_13151429812849 : Nat.Prime 13151429812849 := by
  apply lucas_primality 13151429812849 (14 : ZMod 13151429812849)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (273988121101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (273988121101, 1)] : List FactorBlock).map factorBlockValue).prod) = 13151429812849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_273988121101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (14 : ZMod 13151429812849) ^ 6575714906424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 13151429812849) ^ 4383809937616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (14 : ZMod 13151429812849) ^ 48 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_15646570453571 : Nat.Prime 15646570453571 := by
  apply lucas_primality 15646570453571 (10 : ZMod 15646570453571)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (4889, 1), (45719459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (4889, 1), (45719459, 1)] : List FactorBlock).map factorBlockValue).prod) = 15646570453571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_4889
      · exact prime_oneHundredNineDC_45719459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 15646570453571) ^ 7823285226785 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 15646570453571) ^ 3129314090714 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 15646570453571) ^ 2235224350510 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 15646570453571) ^ 3200362130 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 15646570453571) ^ 342230 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_20628784299661 : Nat.Prime 20628784299661 := by
  apply lucas_primality 20628784299661 (6 : ZMod 20628784299661)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (67, 1), (103, 1), (2930633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (67, 1), (103, 1), (2930633, 1)] : List FactorBlock).map factorBlockValue).prod) = 20628784299661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_103
      · exact prime_oneHundredNineDC_2930633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 20628784299661) ^ 10314392149830 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 6876261433220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 4125756859932 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 1213457899980 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 307892302980 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 200279459220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 20628784299661) ^ 7039020 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_25175211074297 : Nat.Prime 25175211074297 := by
  apply lucas_primality 25175211074297 (3 : ZMod 25175211074297)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (463, 1), (6796763249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (463, 1), (6796763249, 1)] : List FactorBlock).map factorBlockValue).prod) = 25175211074297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_463
      · exact prime_oneHundredNineDC_6796763249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 25175211074297) ^ 12587605537148 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 25175211074297) ^ 54374105992 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 25175211074297) ^ 3704 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_26591484342361 : Nat.Prime 26591484342361 := by
  apply lucas_primality 26591484342361 (19 : ZMod 26591484342361)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (99901, 1), (316879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (99901, 1), (316879, 1)] : List FactorBlock).map factorBlockValue).prod) = 26591484342361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_99901
      · exact prime_oneHundredNineDC_316879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 26591484342361) ^ 13295742171180 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (19 : ZMod 26591484342361) ^ 8863828114120 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (19 : ZMod 26591484342361) ^ 5318296868472 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (19 : ZMod 26591484342361) ^ 3798783477480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (19 : ZMod 26591484342361) ^ 266178360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (19 : ZMod 26591484342361) ^ 83916840 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_30492904204537 : Nat.Prime 30492904204537 := by
  apply lucas_primality 30492904204537 (7 : ZMod 30492904204537)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1270537675189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1270537675189, 1)] : List FactorBlock).map factorBlockValue).prod) = 30492904204537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_1270537675189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 30492904204537) ^ 15246452102268 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 30492904204537) ^ 10164301401512 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 30492904204537) ^ 24 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_30509907221587 : Nat.Prime 30509907221587 := by
  apply lucas_primality 30509907221587 (2 : ZMod 30509907221587)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (313, 1), (1123, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (313, 1), (1123, 1), (85601, 1)] : List FactorBlock).map factorBlockValue).prod) = 30509907221587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_313
      · exact prime_oneHundredNineDC_1123
      · exact prime_oneHundredNineDC_85601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30509907221587) ^ 15254953610793 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30509907221587) ^ 10169969073862 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30509907221587) ^ 2346915940122 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30509907221587) ^ 97475741922 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30509907221587) ^ 27168216582 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30509907221587) ^ 356419986 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_30945338012851 : Nat.Prime 30945338012851 := by
  apply lucas_primality 30945338012851 (3 : ZMod 30945338012851)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (206302253419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (206302253419, 1)] : List FactorBlock).map factorBlockValue).prod) = 30945338012851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_206302253419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 30945338012851) ^ 15472669006425 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30945338012851) ^ 10315112670950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30945338012851) ^ 6189067602570 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 30945338012851) ^ 150 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_31293140907143 : Nat.Prime 31293140907143 := by
  apply lucas_primality 31293140907143 (5 : ZMod 31293140907143)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15646570453571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15646570453571, 1)] : List FactorBlock).map factorBlockValue).prod) = 31293140907143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_15646570453571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 31293140907143) ^ 15646570453571 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 31293140907143) ^ 2 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_34958263295597 : Nat.Prime 34958263295597 := by
  apply lucas_primality 34958263295597 (2 : ZMod 34958263295597)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (727, 1), (324903001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (727, 1), (324903001, 1)] : List FactorBlock).map factorBlockValue).prod) = 34958263295597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_727
      · exact prime_oneHundredNineDC_324903001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34958263295597) ^ 17479131647798 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34958263295597) ^ 944817926908 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34958263295597) ^ 48085644148 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 34958263295597) ^ 107596 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_42378709147013 : Nat.Prime 42378709147013 := by
  apply lucas_primality 42378709147013 (2 : ZMod 42378709147013)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (1513525326679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (1513525326679, 1)] : List FactorBlock).map factorBlockValue).prod) = 42378709147013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_1513525326679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 42378709147013) ^ 21189354573506 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378709147013) ^ 6054101306716 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 42378709147013) ^ 28 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_66787787236439 : Nat.Prime 66787787236439 := by
  apply lucas_primality 66787787236439 (11 : ZMod 66787787236439)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (880259, 1), (37936441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (880259, 1), (37936441, 1)] : List FactorBlock).map factorBlockValue).prod) = 66787787236439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_880259
      · exact prime_oneHundredNineDC_37936441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 66787787236439) ^ 33393893618219 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 66787787236439) ^ 75872882 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 66787787236439) ^ 1760518 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_82865605606961 : Nat.Prime 82865605606961 := by
  apply lucas_primality 82865605606961 (6 : ZMod 82865605606961)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 2), (1409, 1), (6075583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 2), (1409, 1), (6075583, 1)] : List FactorBlock).map factorBlockValue).prod) = 82865605606961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_1409
      · exact prime_oneHundredNineDC_6075583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 82865605606961) ^ 41432802803480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82865605606961) ^ 16573121121392 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82865605606961) ^ 7533236873360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82865605606961) ^ 58811643440 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82865605606961) ^ 13639120 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_83865607902767 : Nat.Prime 83865607902767 := by
  apply lucas_primality 83865607902767 (5 : ZMod 83865607902767)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (306078860959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (306078860959, 1)] : List FactorBlock).map factorBlockValue).prod) = 83865607902767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_137
      · exact prime_oneHundredNineDC_306078860959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 83865607902767) ^ 41932803951383 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 83865607902767) ^ 612157721918 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 83865607902767) ^ 274 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_85118019075161 : Nat.Prime 85118019075161 := by
  apply lucas_primality 85118019075161 (3 : ZMod 85118019075161)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (73377602651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (73377602651, 1)] : List FactorBlock).map factorBlockValue).prod) = 85118019075161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_73377602651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 85118019075161) ^ 42559009537580 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85118019075161) ^ 17023603815032 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85118019075161) ^ 2935104106040 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 85118019075161) ^ 1160 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_93341986962317 : Nat.Prime 93341986962317 := by
  apply lucas_primality 93341986962317 (2 : ZMod 93341986962317)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19421, 1), (1201559999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19421, 1), (1201559999, 1)] : List FactorBlock).map factorBlockValue).prod) = 93341986962317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_19421
      · exact prime_oneHundredNineDC_1201559999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 93341986962317) ^ 46670993481158 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 93341986962317) ^ 4806239996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 93341986962317) ^ 77684 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_148590939321707 : Nat.Prime 148590939321707 := by
  apply lucas_primality 148590939321707 (5 : ZMod 148590939321707)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (558612553841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (558612553841, 1)] : List FactorBlock).map factorBlockValue).prod) = 148590939321707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_558612553841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 148590939321707) ^ 74295469660853 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 148590939321707) ^ 21227277045958 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 148590939321707) ^ 7820575753774 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 148590939321707) ^ 266 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_199975014078583 : Nat.Prime 199975014078583 := by
  apply lucas_primality 199975014078583 (3 : ZMod 199975014078583)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (941, 1), (1213, 1), (1536811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (941, 1), (1213, 1), (1536811, 1)] : List FactorBlock).map factorBlockValue).prod) = 199975014078583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_941
      · exact prime_oneHundredNineDC_1213
      · exact prime_oneHundredNineDC_1536811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 199975014078583) ^ 99987507039291 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 199975014078583) ^ 66658338026194 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 199975014078583) ^ 10525000740978 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 199975014078583) ^ 212513298702 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 199975014078583) ^ 164859863214 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 199975014078583) ^ 130123362 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_201538104053593 : Nat.Prime 201538104053593 := by
  apply lucas_primality 201538104053593 (5 : ZMod 201538104053593)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8397421002233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8397421002233, 1)] : List FactorBlock).map factorBlockValue).prod) = 201538104053593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_8397421002233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 201538104053593) ^ 100769052026796 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 201538104053593) ^ 67179368017864 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 201538104053593) ^ 24 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_232070731675553 : Nat.Prime 232070731675553 := by
  apply lucas_primality 232070731675553 (5 : ZMod 232070731675553)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (11, 1), (151, 1), (257, 1), (467, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (11, 1), (151, 1), (257, 1), (467, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) = 232070731675553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_151
      · exact prime_oneHundredNineDC_257
      · exact prime_oneHundredNineDC_467
      · exact prime_oneHundredNineDC_5197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 232070731675553) ^ 116035365837776 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 33152961667936 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 21097339243232 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 1536892262752 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 902998955936 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 496939468256 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 232070731675553) ^ 44654749216 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_236366498083921 : Nat.Prime 236366498083921 := by
  apply lucas_primality 236366498083921 (17 : ZMod 236366498083921)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (55603, 1), (17712361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (55603, 1), (17712361, 1)] : List FactorBlock).map factorBlockValue).prod) = 236366498083921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_55603
      · exact prime_oneHundredNineDC_17712361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 236366498083921) ^ 118183249041960 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 236366498083921) ^ 78788832694640 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 236366498083921) ^ 47273299616784 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 236366498083921) ^ 4250966640 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (17 : ZMod 236366498083921) ^ 13344720 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_240147847125647 : Nat.Prime 240147847125647 := by
  apply lucas_primality 240147847125647 (5 : ZMod 240147847125647)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (6319680187517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (6319680187517, 1)] : List FactorBlock).map factorBlockValue).prod) = 240147847125647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_6319680187517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 240147847125647) ^ 120073923562823 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 240147847125647) ^ 12639360375034 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 240147847125647) ^ 38 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_332560963881613 : Nat.Prime 332560963881613 := by
  apply lucas_primality 332560963881613 (2 : ZMod 332560963881613)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (19, 1), (59, 1), (2746894009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (19, 1), (59, 1), (2746894009, 1)] : List FactorBlock).map factorBlockValue).prod) = 332560963881613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_2746894009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 332560963881613) ^ 166280481940806 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 332560963881613) ^ 110853654627204 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 332560963881613) ^ 17503208625348 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 332560963881613) ^ 5636626506468 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 332560963881613) ^ 121068 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_351981542233897 : Nat.Prime 351981542233897 := by
  apply lucas_primality 351981542233897 (10 : ZMod 351981542233897)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1402901, 1), (10453979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1402901, 1), (10453979, 1)] : List FactorBlock).map factorBlockValue).prod) = 351981542233897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_1402901
      · exact prime_oneHundredNineDC_10453979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 351981542233897) ^ 175990771116948 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 351981542233897) ^ 117327180744632 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 351981542233897) ^ 250895496 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 351981542233897) ^ 33669624 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_662872049283869 : Nat.Prime 662872049283869 := by
  apply lucas_primality 662872049283869 (2 : ZMod 662872049283869)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (97, 1), (1708433116711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (97, 1), (1708433116711, 1)] : List FactorBlock).map factorBlockValue).prod) = 662872049283869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_97
      · exact prime_oneHundredNineDC_1708433116711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 662872049283869) ^ 331436024641934 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 662872049283869) ^ 6833732466844 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 662872049283869) ^ 388 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_837649869302669 : Nat.Prime 837649869302669 := by
  apply lucas_primality 837649869302669 (2 : ZMod 837649869302669)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (601, 1), (997, 1), (349488511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (601, 1), (997, 1), (349488511, 1)] : List FactorBlock).map factorBlockValue).prod) = 837649869302669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_601
      · exact prime_oneHundredNineDC_997
      · exact prime_oneHundredNineDC_349488511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 837649869302669) ^ 418824934651334 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 837649869302669) ^ 1393760181868 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 837649869302669) ^ 840170380444 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 837649869302669) ^ 2396788 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1293038565657193 : Nat.Prime 1293038565657193 := by
  apply lucas_primality 1293038565657193 (5 : ZMod 1293038565657193)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (6367, 1), (2820617083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (6367, 1), (2820617083, 1)] : List FactorBlock).map factorBlockValue).prod) = 1293038565657193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_6367
      · exact prime_oneHundredNineDC_2820617083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1293038565657193) ^ 646519282828596 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293038565657193) ^ 431012855219064 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293038565657193) ^ 203084429976 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1293038565657193) ^ 458424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1586908108739731 : Nat.Prime 1586908108739731 := by
  apply lucas_primality 1586908108739731 (3 : ZMod 1586908108739731)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (103516510681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (73, 1), (103516510681, 1)] : List FactorBlock).map factorBlockValue).prod) = 1586908108739731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_103516510681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1586908108739731) ^ 793454054369865 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1586908108739731) ^ 528969369579910 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1586908108739731) ^ 317381621747946 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1586908108739731) ^ 226701158391390 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1586908108739731) ^ 21738467243010 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1586908108739731) ^ 15330 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1635049154787031 : Nat.Prime 1635049154787031 := by
  apply lucas_primality 1635049154787031 (3 : ZMod 1635049154787031)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (414461, 1), (43833347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (414461, 1), (43833347, 1)] : List FactorBlock).map factorBlockValue).prod) = 1635049154787031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_414461
      · exact prime_oneHundredNineDC_43833347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1635049154787031) ^ 817524577393515 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1635049154787031) ^ 545016384929010 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1635049154787031) ^ 327009830957406 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1635049154787031) ^ 3945001230 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1635049154787031) ^ 37301490 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1638168468925831 : Nat.Prime 1638168468925831 := by
  apply lucas_primality 1638168468925831 (3 : ZMod 1638168468925831)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (277, 1), (4584469451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (277, 1), (4584469451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1638168468925831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_277
      · exact prime_oneHundredNineDC_4584469451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1638168468925831) ^ 819084234462915 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1638168468925831) ^ 546056156308610 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1638168468925831) ^ 327633693785166 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1638168468925831) ^ 38096941137810 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1638168468925831) ^ 5913965591790 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1638168468925831) ^ 357330 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1948762409580643 : Nat.Prime 1948762409580643 := by
  apply lucas_primality 1948762409580643 (2 : ZMod 1948762409580643)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (18743, 1), (17328801949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (18743, 1), (17328801949, 1)] : List FactorBlock).map factorBlockValue).prod) = 1948762409580643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_18743
      · exact prime_oneHundredNineDC_17328801949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1948762409580643) ^ 974381204790321 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1948762409580643) ^ 649587469860214 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1948762409580643) ^ 103972811694 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1948762409580643) ^ 112458 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1961221105826453 : Nat.Prime 1961221105826453 := by
  apply lucas_primality 1961221105826453 (3 : ZMod 1961221105826453)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (8543, 1), (3376037323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (8543, 1), (3376037323, 1)] : List FactorBlock).map factorBlockValue).prod) = 1961221105826453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_8543
      · exact prime_oneHundredNineDC_3376037323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1961221105826453) ^ 980610552913226 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1961221105826453) ^ 115365947401556 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1961221105826453) ^ 229570537964 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1961221105826453) ^ 580924 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2859716801348971 : Nat.Prime 2859716801348971 := by
  apply lucas_primality 2859716801348971 (2 : ZMod 2859716801348971)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (109, 1), (874531131911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (109, 1), (874531131911, 1)] : List FactorBlock).map factorBlockValue).prod) = 2859716801348971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_109
      · exact prime_oneHundredNineDC_874531131911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2859716801348971) ^ 1429858400674485 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2859716801348971) ^ 953238933782990 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2859716801348971) ^ 571943360269794 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2859716801348971) ^ 26235933957330 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2859716801348971) ^ 3270 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_3092001443374703 : Nat.Prime 3092001443374703 := by
  apply lucas_primality 3092001443374703 (5 : ZMod 3092001443374703)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (152029, 1), (77626849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (152029, 1), (77626849, 1)] : List FactorBlock).map factorBlockValue).prod) = 3092001443374703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_131
      · exact prime_oneHundredNineDC_152029
      · exact prime_oneHundredNineDC_77626849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3092001443374703) ^ 1546000721687351 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3092001443374703) ^ 23603064453242 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3092001443374703) ^ 20338234438 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 3092001443374703) ^ 39831598 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4962134260473197 : Nat.Prime 4962134260473197 := by
  apply lucas_primality 4962134260473197 (2 : ZMod 4962134260473197)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1307, 1), (336113, 1), (2823889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1307, 1), (336113, 1), (2823889, 1)] : List FactorBlock).map factorBlockValue).prod) = 4962134260473197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_1307
      · exact prime_oneHundredNineDC_336113
      · exact prime_oneHundredNineDC_2823889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4962134260473197) ^ 2481067130236598 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962134260473197) ^ 3796583213828 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962134260473197) ^ 14763291692 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4962134260473197) ^ 1757198764 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_5951798399156431 : Nat.Prime 5951798399156431 := by
  apply lucas_primality 5951798399156431 (6 : ZMod 5951798399156431)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (47, 1), (4221133616423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (47, 1), (4221133616423, 1)] : List FactorBlock).map factorBlockValue).prod) = 5951798399156431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_47
      · exact prime_oneHundredNineDC_4221133616423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 5951798399156431) ^ 2975899199578215 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5951798399156431) ^ 1983932799718810 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5951798399156431) ^ 1190359679831286 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5951798399156431) ^ 126634008492690 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 5951798399156431) ^ 1410 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_24159822937935913 : Nat.Prime 24159822937935913 := by
  apply lucas_primality 24159822937935913 (5 : ZMod 24159822937935913)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (52889, 1), (6344477989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (52889, 1), (6344477989, 1)] : List FactorBlock).map factorBlockValue).prod) = 24159822937935913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_52889
      · exact prime_oneHundredNineDC_6344477989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24159822937935913) ^ 12079911468967956 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24159822937935913) ^ 8053274312645304 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24159822937935913) ^ 456802415208 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 24159822937935913) ^ 3808008 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_31608168845812331 : Nat.Prime 31608168845812331 := by
  apply lucas_primality 31608168845812331 (2 : ZMod 31608168845812331)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (1531, 1), (38953660631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (1531, 1), (38953660631, 1)] : List FactorBlock).map factorBlockValue).prod) = 31608168845812331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_1531
      · exact prime_oneHundredNineDC_38953660631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31608168845812331) ^ 15804084422906165 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31608168845812331) ^ 6321633769162466 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31608168845812331) ^ 596380544260610 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31608168845812331) ^ 20645440134430 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 31608168845812331) ^ 811430 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_36041447974071791 : Nat.Prime 36041447974071791 := by
  apply lucas_primality 36041447974071791 (11 : ZMod 36041447974071791)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (373, 1), (9662586588223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (373, 1), (9662586588223, 1)] : List FactorBlock).map factorBlockValue).prod) = 36041447974071791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_373
      · exact prime_oneHundredNineDC_9662586588223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 36041447974071791) ^ 18020723987035895 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 36041447974071791) ^ 7208289594814358 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 36041447974071791) ^ 96625865882230 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 36041447974071791) ^ 3730 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_37038303625810373 : Nat.Prime 37038303625810373 := by
  apply lucas_primality 37038303625810373 (2 : ZMod 37038303625810373)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (6563611, 1), (12942607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (6563611, 1), (12942607, 1)] : List FactorBlock).map factorBlockValue).prod) = 37038303625810373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_109
      · exact prime_oneHundredNineDC_6563611
      · exact prime_oneHundredNineDC_12942607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37038303625810373) ^ 18519151812905186 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37038303625810373) ^ 339800950695508 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37038303625810373) ^ 5642976652 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37038303625810373) ^ 2861734396 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_37174678936731907 : Nat.Prime 37174678936731907 := by
  apply lucas_primality 37174678936731907 (2 : ZMod 37174678936731907)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7537, 1), (10253, 1), (80176391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7537, 1), (10253, 1), (80176391, 1)] : List FactorBlock).map factorBlockValue).prod) = 37174678936731907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7537
      · exact prime_oneHundredNineDC_10253
      · exact prime_oneHundredNineDC_80176391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37174678936731907) ^ 18587339468365953 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37174678936731907) ^ 12391559645577302 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37174678936731907) ^ 4932291221538 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37174678936731907) ^ 3625736753802 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 37174678936731907) ^ 463661166 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_116710414561575181 : Nat.Prime 116710414561575181 := by
  apply lucas_primality 116710414561575181 (2 : ZMod 116710414561575181)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (29, 1), (186727, 1), (119737997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (29, 1), (186727, 1), (119737997, 1)] : List FactorBlock).map factorBlockValue).prod) = 116710414561575181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_186727
      · exact prime_oneHundredNineDC_119737997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 116710414561575181) ^ 58355207280787590 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 116710414561575181) ^ 38903471520525060 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 116710414561575181) ^ 23342082912315036 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 116710414561575181) ^ 4024497053847420 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 116710414561575181) ^ 625032344340 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 116710414561575181) ^ 974714940 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_117411864683600537 : Nat.Prime 117411864683600537 := by
  apply lucas_primality 117411864683600537 (3 : ZMod 117411864683600537)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (67, 1), (31293140907143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (67, 1), (31293140907143, 1)] : List FactorBlock).map factorBlockValue).prod) = 117411864683600537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_31293140907143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 117411864683600537) ^ 58705932341800268 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 117411864683600537) ^ 16773123526228648 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 117411864683600537) ^ 1752415890800008 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 117411864683600537) ^ 3752 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_118595487448045369 : Nat.Prime 118595487448045369 := by
  apply lucas_primality 118595487448045369 (7 : ZMod 118595487448045369)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (79, 1), (39107, 1), (533155723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (79, 1), (39107, 1), (533155723, 1)] : List FactorBlock).map factorBlockValue).prod) = 118595487448045369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_79
      · exact prime_oneHundredNineDC_39107
      · exact prime_oneHundredNineDC_533155723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 118595487448045369) ^ 59297743724022684 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 118595487448045369) ^ 39531829149348456 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 118595487448045369) ^ 1501208701873992 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 118595487448045369) ^ 3032589752424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 118595487448045369) ^ 222440616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_167474750814600797 : Nat.Prime 167474750814600797 := by
  apply lucas_primality 167474750814600797 (2 : ZMod 167474750814600797)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (313, 1), (1277, 1), (40283, 1), (371479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (313, 1), (1277, 1), (40283, 1), (371479, 1)] : List FactorBlock).map factorBlockValue).prod) = 167474750814600797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_313
      · exact prime_oneHundredNineDC_1277
      · exact prime_oneHundredNineDC_40283
      · exact prime_oneHundredNineDC_371479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 167474750814600797) ^ 83737375407300398 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 167474750814600797) ^ 23924964402085828 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 167474750814600797) ^ 535063101644092 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 167474750814600797) ^ 131147024913548 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 167474750814600797) ^ 4157454777812 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 167474750814600797) ^ 450832350724 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_168799809564238849 : Nat.Prime 168799809564238849 := by
  apply lucas_primality 168799809564238849 (11 : ZMod 168799809564238849)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (3, 1), (19, 1), (2891992351361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (3, 1), (19, 1), (2891992351361, 1)] : List FactorBlock).map factorBlockValue).prod) = 168799809564238849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_2891992351361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 168799809564238849) ^ 84399904782119424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 168799809564238849) ^ 56266603188079616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 168799809564238849) ^ 8884200503380992 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 168799809564238849) ^ 58368 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_197634173500521977 : Nat.Prime 197634173500521977 := by
  apply lucas_primality 197634173500521977 (3 : ZMod 197634173500521977)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (71, 1), (107, 1), (271, 1), (11999430581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (71, 1), (107, 1), (271, 1), (11999430581, 1)] : List FactorBlock).map factorBlockValue).prod) = 197634173500521977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_71
      · exact prime_oneHundredNineDC_107
      · exact prime_oneHundredNineDC_271
      · exact prime_oneHundredNineDC_11999430581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 197634173500521977) ^ 98817086750260988 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 197634173500521977) ^ 2783579908458056 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 197634173500521977) ^ 1847048350472168 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 197634173500521977) ^ 729277392990856 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 197634173500521977) ^ 16470296 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_348094973803951229 : Nat.Prime 348094973803951229 := by
  apply lucas_primality 348094973803951229 (2 : ZMod 348094973803951229)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (36373, 1), (2392536866659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (36373, 1), (2392536866659, 1)] : List FactorBlock).map factorBlockValue).prod) = 348094973803951229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_36373
      · exact prime_oneHundredNineDC_2392536866659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 348094973803951229) ^ 174047486901975614 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 348094973803951229) ^ 9570147466636 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 348094973803951229) ^ 145492 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_674660060404299833 : Nat.Prime 674660060404299833 := by
  apply lucas_primality 674660060404299833 (3 : ZMod 674660060404299833)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43, 1), (1961221105826453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43, 1), (1961221105826453, 1)] : List FactorBlock).map factorBlockValue).prod) = 674660060404299833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_1961221105826453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 674660060404299833) ^ 337330030202149916 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 674660060404299833) ^ 15689768846611624 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 674660060404299833) ^ 344 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_762952983087953923 : Nat.Prime 762952983087953923 := by
  apply lucas_primality 762952983087953923 (3 : ZMod 762952983087953923)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (199, 1), (449, 1), (129376209367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (199, 1), (449, 1), (129376209367, 1)] : List FactorBlock).map factorBlockValue).prod) = 762952983087953923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_199
      · exact prime_oneHundredNineDC_449
      · exact prime_oneHundredNineDC_129376209367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 762952983087953923) ^ 381476491543976961 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 762952983087953923) ^ 254317661029317974 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 762952983087953923) ^ 69359362098904902 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 762952983087953923) ^ 3833934588381678 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 762952983087953923) ^ 1699227133826178 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 762952983087953923) ^ 5897166 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1089664326928454681 : Nat.Prime 1089664326928454681 := by
  apply lucas_primality 1089664326928454681 (3 : ZMod 1089664326928454681)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (6466133, 1), (324074423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (6466133, 1), (324074423, 1)] : List FactorBlock).map factorBlockValue).prod) = 1089664326928454681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_6466133
      · exact prime_oneHundredNineDC_324074423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1089664326928454681) ^ 544832163464227340 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1089664326928454681) ^ 217932865385690936 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1089664326928454681) ^ 83820332840650360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1089664326928454681) ^ 168518699960 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1089664326928454681) ^ 3362389160 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1143551009668998589 : Nat.Prime 1143551009668998589 := by
  apply lucas_primality 1143551009668998589 (2 : ZMod 1143551009668998589)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (163, 1), (3989, 1), (1231617053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (163, 1), (3989, 1), (1231617053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143551009668998589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_163
      · exact prime_oneHundredNineDC_3989
      · exact prime_oneHundredNineDC_1231617053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1143551009668998589) ^ 571775504834499294 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 381183669889666196 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 163364429952714084 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 67267706451117564 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 7015650366067476 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 286676111724492 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1143551009668998589) ^ 928495596 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1185954874480453691 : Nat.Prime 1185954874480453691 := by
  apply lucas_primality 1185954874480453691 (2 : ZMod 1185954874480453691)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (118595487448045369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (118595487448045369, 1)] : List FactorBlock).map factorBlockValue).prod) = 1185954874480453691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_118595487448045369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1185954874480453691) ^ 592977437240226845 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185954874480453691) ^ 237190974896090738 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1185954874480453691) ^ 10 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1416741397767459763 : Nat.Prime 1416741397767459763 := by
  apply lucas_primality 1416741397767459763 (2 : ZMod 1416741397767459763)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (521, 1), (319049, 1), (26802071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (521, 1), (319049, 1), (26802071, 1)] : List FactorBlock).map factorBlockValue).prod) = 1416741397767459763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_521
      · exact prime_oneHundredNineDC_319049
      · exact prime_oneHundredNineDC_26802071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1416741397767459763) ^ 708370698883729881 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1416741397767459763) ^ 472247132589153254 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1416741397767459763) ^ 26730969769197354 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1416741397767459763) ^ 2719273316252322 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1416741397767459763) ^ 4440513519138 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1416741397767459763) ^ 52859400222 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1611408258542110373 : Nat.Prime 1611408258542110373 := by
  apply lucas_primality 1611408258542110373 (2 : ZMod 1611408258542110373)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (131, 1), (7127, 1), (203381, 1), (2121569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (131, 1), (7127, 1), (203381, 1), (2121569, 1)] : List FactorBlock).map factorBlockValue).prod) = 1611408258542110373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_131
      · exact prime_oneHundredNineDC_7127
      · exact prime_oneHundredNineDC_203381
      · exact prime_oneHundredNineDC_2121569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1611408258542110373) ^ 805704129271055186 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611408258542110373) ^ 12300826401084812 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611408258542110373) ^ 226099096189436 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611408258542110373) ^ 7923101265812 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1611408258542110373) ^ 759536106788 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1932375736319468743 : Nat.Prime 1932375736319468743 := by
  apply lucas_primality 1932375736319468743 (3 : ZMod 1932375736319468743)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (77773027, 1), (1380352697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (77773027, 1), (1380352697, 1)] : List FactorBlock).map factorBlockValue).prod) = 1932375736319468743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_77773027
      · exact prime_oneHundredNineDC_1380352697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1932375736319468743) ^ 966187868159734371 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932375736319468743) ^ 644125245439822914 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932375736319468743) ^ 24846348546 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 1932375736319468743) ^ 1399914486 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4042121515058747971 : Nat.Prime 4042121515058747971 := by
  apply lucas_primality 4042121515058747971 (7 : ZMod 4042121515058747971)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (43, 1), (241, 1), (57349, 1), (25190353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (43, 1), (241, 1), (57349, 1), (25190353, 1)] : List FactorBlock).map factorBlockValue).prod) = 4042121515058747971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_241
      · exact prime_oneHundredNineDC_57349
      · exact prime_oneHundredNineDC_25190353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4042121515058747971) ^ 2021060757529373985 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 1347373838352915990 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 808424303011749594 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 94002825931598790 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 16772288444227170 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 70482859597530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 4042121515058747971) ^ 160463075490 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7002699491740629151 : Nat.Prime 7002699491740629151 := by
  apply lucas_primality 7002699491740629151 (3 : ZMod 7002699491740629151)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (233, 1), (66787787236439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (233, 1), (66787787236439, 1)] : List FactorBlock).map factorBlockValue).prod) = 7002699491740629151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_233
      · exact prime_oneHundredNineDC_66787787236439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7002699491740629151) ^ 3501349745870314575 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7002699491740629151) ^ 2334233163913543050 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7002699491740629151) ^ 1400539898348125830 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7002699491740629151) ^ 30054504256397550 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7002699491740629151) ^ 104850 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7591808733673221703 : Nat.Prime 7591808733673221703 := by
  apply lucas_primality 7591808733673221703 (3 : ZMod 7591808733673221703)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (57131, 1), (7382457017569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (57131, 1), (7382457017569, 1)] : List FactorBlock).map factorBlockValue).prod) = 7591808733673221703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_57131
      · exact prime_oneHundredNineDC_7382457017569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7591808733673221703) ^ 3795904366836610851 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7591808733673221703) ^ 2530602911224407234 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7591808733673221703) ^ 132884226316242 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 7591808733673221703) ^ 1028358 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_14087916018797859443 : Nat.Prime 14087916018797859443 := by
  apply lucas_primality 14087916018797859443 (2 : ZMod 14087916018797859443)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (1753, 1), (236366498083921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (1753, 1), (236366498083921, 1)] : List FactorBlock).map factorBlockValue).prod) = 14087916018797859443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_1753
      · exact prime_oneHundredNineDC_236366498083921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14087916018797859443) ^ 7043958009398929721 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 14087916018797859443) ^ 828700942282227026 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 14087916018797859443) ^ 8036460934853314 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 14087916018797859443) ^ 59602 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_51489371927641184401 : Nat.Prime 51489371927641184401 := by
  apply lucas_primality 51489371927641184401 (13 : ZMod 51489371927641184401)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (17, 1), (31, 1), (61, 1), (977, 1), (25913, 1), (52721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (17, 1), (31, 1), (61, 1), (977, 1), (25913, 1), (52721, 1)] : List FactorBlock).map factorBlockValue).prod) = 51489371927641184401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_61
      · exact prime_oneHundredNineDC_977
      · exact prime_oneHundredNineDC_25913
      · exact prime_oneHundredNineDC_52721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 51489371927641184401) ^ 25744685963820592200 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 17163123975880394800 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 10297874385528236880 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 3028786583978893200 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 1660947481536812400 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 844088064387560400 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 52701506578957200 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 1987009297558800 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (13 : ZMod 51489371927641184401) ^ 976638757376400 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_169054992225574313317 : Nat.Prime 169054992225574313317 := by
  apply lucas_primality 169054992225574313317 (2 : ZMod 169054992225574313317)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (14087916018797859443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (14087916018797859443, 1)] : List FactorBlock).map factorBlockValue).prod) = 169054992225574313317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_14087916018797859443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 169054992225574313317) ^ 84527496112787156658 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 169054992225574313317) ^ 56351664075191437772 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 169054992225574313317) ^ 12 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_269109864282865450303 : Nat.Prime 269109864282865450303 := by
  apply lucas_primality 269109864282865450303 (3 : ZMod 269109864282865450303)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (677, 1), (5227, 1), (64109, 1), (65901749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (677, 1), (5227, 1), (64109, 1), (65901749, 1)] : List FactorBlock).map factorBlockValue).prod) = 269109864282865450303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_677
      · exact prime_oneHundredNineDC_5227
      · exact prime_oneHundredNineDC_64109
      · exact prime_oneHundredNineDC_65901749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 269109864282865450303) ^ 134554932141432725151 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 269109864282865450303) ^ 89703288094288483434 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 269109864282865450303) ^ 397503492293745126 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 269109864282865450303) ^ 51484573231847226 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 269109864282865450303) ^ 4197692434492278 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 269109864282865450303) ^ 4083501096198 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_273995042908487573021 : Nat.Prime 273995042908487573021 := by
  apply lucas_primality 273995042908487573021 (2 : ZMod 273995042908487573021)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (619, 1), (15511, 1), (1426862956439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (619, 1), (15511, 1), (1426862956439, 1)] : List FactorBlock).map factorBlockValue).prod) = 273995042908487573021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_619
      · exact prime_oneHundredNineDC_15511
      · exact prime_oneHundredNineDC_1426862956439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 273995042908487573021) ^ 136997521454243786510 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273995042908487573021) ^ 54799008581697514604 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273995042908487573021) ^ 442641426346506580 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273995042908487573021) ^ 17664563400714820 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 273995042908487573021) ^ 192026180 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_456970054626929619653 : Nat.Prime 456970054626929619653 := by
  apply lucas_primality 456970054626929619653 (2 : ZMod 456970054626929619653)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (53, 1), (121229, 1), (613122649781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (53, 1), (121229, 1), (613122649781, 1)] : List FactorBlock).map factorBlockValue).prod) = 456970054626929619653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_121229
      · exact prime_oneHundredNineDC_613122649781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 456970054626929619653) ^ 228485027313464809826 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 456970054626929619653) ^ 15757588090583779988 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 456970054626929619653) ^ 8622076502394898484 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 456970054626929619653) ^ 3769478050853588 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 456970054626929619653) ^ 745315892 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1138871411428638180211 : Nat.Prime 1138871411428638180211 := by
  apply lucas_primality 1138871411428638180211 (15 : ZMod 1138871411428638180211)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (41, 1), (43, 1), (67, 1), (251, 1), (1487, 1), (3359, 1), (256349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (41, 1), (43, 1), (67, 1), (251, 1), (1487, 1), (3359, 1), (256349, 1)] : List FactorBlock).map factorBlockValue).prod) = 1138871411428638180211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_41
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_251
      · exact prime_oneHundredNineDC_1487
      · exact prime_oneHundredNineDC_3359
      · exact prime_oneHundredNineDC_256349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 1138871411428638180211) ^ 569435705714319090105 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 379623803809546060070 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 227774282285727636042 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 27777351498259467810 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 26485381661131120470 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 16998080767591614630 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 4537336300512502710 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 765885280046158830 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 339050732786138190 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 1138871411428638180211) ^ 4442659856011290 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2148389467862699569061 : Nat.Prime 2148389467862699569061 := by
  apply lucas_primality 2148389467862699569061 (2 : ZMod 2148389467862699569061)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (15199, 1), (818887, 1), (1232951483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (15199, 1), (818887, 1), (1232951483, 1)] : List FactorBlock).map factorBlockValue).prod) = 2148389467862699569061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_15199
      · exact prime_oneHundredNineDC_818887
      · exact prime_oneHundredNineDC_1232951483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2148389467862699569061) ^ 1074194733931349784530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148389467862699569061) ^ 429677893572539913812 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148389467862699569061) ^ 306912781123242795580 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148389467862699569061) ^ 141350711748318940 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148389467862699569061) ^ 2623548142616380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 2148389467862699569061) ^ 1742476891820 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2814694771975911517967 : Nat.Prime 2814694771975911517967 := by
  apply lucas_primality 2814694771975911517967 (5 : ZMod 2814694771975911517967)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (607, 1), (55843, 1), (265511, 1), (1718383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (607, 1), (55843, 1), (265511, 1), (1718383, 1)] : List FactorBlock).map factorBlockValue).prod) = 2814694771975911517967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_607
      · exact prime_oneHundredNineDC_55843
      · exact prime_oneHundredNineDC_265511
      · exact prime_oneHundredNineDC_1718383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2814694771975911517967) ^ 1407347385987955758983 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 402099253139415931138 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 216514982459685501382 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 4637058932415010738 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 50403717063479962 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 10601047685315906 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2814694771975911517967) ^ 1637990350216402 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7362717547288839274751 : Nat.Prime 7362717547288839274751 := by
  apply lucas_primality 7362717547288839274751 (7 : ZMod 7362717547288839274751)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (19, 1), (50833, 1), (30492904204537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (19, 1), (50833, 1), (30492904204537, 1)] : List FactorBlock).map factorBlockValue).prod) = 7362717547288839274751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_50833
      · exact prime_oneHundredNineDC_30492904204537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7362717547288839274751) ^ 3681358773644419637375 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 7362717547288839274751) ^ 1472543509457767854950 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 7362717547288839274751) ^ 387511449857307330250 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 7362717547288839274751) ^ 144841294971550750 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 7362717547288839274751) ^ 241456750 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_7670598502167253096403 : Nat.Prime 7670598502167253096403 := by
  apply lucas_primality 7670598502167253096403 (2 : ZMod 7670598502167253096403)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (239, 1), (557, 1), (689987, 1), (112546331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (239, 1), (557, 1), (689987, 1), (112546331, 1)] : List FactorBlock).map factorBlockValue).prod) = 7670598502167253096403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_239
      · exact prime_oneHundredNineDC_557
      · exact prime_oneHundredNineDC_689987
      · exact prime_oneHundredNineDC_112546331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7670598502167253096403) ^ 3835299251083626548201 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 1095799786023893299486 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 144728273625797228234 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 32094554402373443918 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 13771271996709610586 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 11117018874511046 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 7670598502167253096403) ^ 68155029435542 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_8468272625735537674757 : Nat.Prime 8468272625735537674757 := by
  apply lucas_primality 8468272625735537674757 (2 : ZMod 8468272625735537674757)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (643, 1), (4967, 1), (662872049283869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (643, 1), (4967, 1), (662872049283869, 1)] : List FactorBlock).map factorBlockValue).prod) = 8468272625735537674757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_643
      · exact prime_oneHundredNineDC_4967
      · exact prime_oneHundredNineDC_662872049283869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8468272625735537674757) ^ 4234136312867768837378 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8468272625735537674757) ^ 13169941875171909292 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8468272625735537674757) ^ 1704906910758111068 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 8468272625735537674757) ^ 12775124 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_9793816795723032830489 : Nat.Prime 9793816795723032830489 := by
  apply lucas_primality 9793816795723032830489 (3 : ZMod 9793816795723032830489)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (2887, 1), (7682911, 1), (2399725501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (2887, 1), (7682911, 1), (2399725501, 1)] : List FactorBlock).map factorBlockValue).prod) = 9793816795723032830489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_2887
      · exact prime_oneHundredNineDC_7682911
      · exact prime_oneHundredNineDC_2399725501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9793816795723032830489) ^ 4896908397861516415244 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9793816795723032830489) ^ 425818121553175340456 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9793816795723032830489) ^ 3392385450544867624 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9793816795723032830489) ^ 1274753383935208 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 9793816795723032830489) ^ 4081223786488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_23758638049562527465609 : Nat.Prime 23758638049562527465609 := by
  apply lucas_primality 23758638049562527465609 (7 : ZMod 23758638049562527465609)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (257, 1), (167474750814600797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (257, 1), (167474750814600797, 1)] : List FactorBlock).map factorBlockValue).prod) = 23758638049562527465609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_257
      · exact prime_oneHundredNineDC_167474750814600797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23758638049562527465609) ^ 11879319024781263732804 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23758638049562527465609) ^ 7919546016520842488536 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23758638049562527465609) ^ 1032984263024457715896 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23758638049562527465609) ^ 92446062449659639944 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 23758638049562527465609) ^ 141864 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_30399928466956379847211 : Nat.Prime 30399928466956379847211 := by
  apply lucas_primality 30399928466956379847211 (2 : ZMod 30399928466956379847211)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (109, 1), (251, 1), (37038303625810373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (109, 1), (251, 1), (37038303625810373, 1)] : List FactorBlock).map factorBlockValue).prod) = 30399928466956379847211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_109
      · exact prime_oneHundredNineDC_251
      · exact prime_oneHundredNineDC_37038303625810373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30399928466956379847211) ^ 15199964233478189923605 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30399928466956379847211) ^ 10133309488985459949070 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30399928466956379847211) ^ 6079985693391275969442 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30399928466956379847211) ^ 278898426302352108690 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30399928466956379847211) ^ 121115252856399919710 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 30399928466956379847211) ^ 820770 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_52616981360587225057607 : Nat.Prime 52616981360587225057607 := by
  apply lucas_primality 52616981360587225057607 (5 : ZMod 52616981360587225057607)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (509, 1), (1901, 1), (706801, 1), (2959071959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (509, 1), (1901, 1), (706801, 1), (2959071959, 1)] : List FactorBlock).map factorBlockValue).prod) = 52616981360587225057607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_509
      · exact prime_oneHundredNineDC_1901
      · exact prime_oneHundredNineDC_706801
      · exact prime_oneHundredNineDC_2959071959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52616981360587225057607) ^ 26308490680293612528803 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52616981360587225057607) ^ 4047460104660555773662 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52616981360587225057607) ^ 103373244323354076734 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52616981360587225057607) ^ 27678580410619266206 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52616981360587225057607) ^ 74443841138576806 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 52616981360587225057607) ^ 17781582229034 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_77502291602841340499809 : Nat.Prime 77502291602841340499809 := by
  apply lucas_primality 77502291602841340499809 (7 : ZMod 77502291602841340499809)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (167, 1), (1611408258542110373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (167, 1), (1611408258542110373, 1)] : List FactorBlock).map factorBlockValue).prod) = 77502291602841340499809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_167
      · exact prime_oneHundredNineDC_1611408258542110373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 77502291602841340499809) ^ 38751145801420670249904 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 77502291602841340499809) ^ 25834097200947113499936 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 77502291602841340499809) ^ 464085578460127787424 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 77502291602841340499809) ^ 48096 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_81638799778782583624319 : Nat.Prime 81638799778782583624319 := by
  apply lucas_primality 81638799778782583624319 (7 : ZMod 81638799778782583624319)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (2148389467862699569061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (2148389467862699569061, 1)] : List FactorBlock).map factorBlockValue).prod) = 81638799778782583624319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_2148389467862699569061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 81638799778782583624319) ^ 40819399889391291812159 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 81638799778782583624319) ^ 4296778935725399138122 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 81638799778782583624319) ^ 38 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_110723210098067601022057 : Nat.Prime 110723210098067601022057 := by
  apply lucas_primality 110723210098067601022057 (15 : ZMod 110723210098067601022057)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (37, 1), (67, 1), (107, 1), (3490703, 1), (4982579341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (37, 1), (67, 1), (107, 1), (3490703, 1), (4982579341, 1)] : List FactorBlock).map factorBlockValue).prod) = 110723210098067601022057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_67
      · exact prime_oneHundredNineDC_107
      · exact prime_oneHundredNineDC_3490703
      · exact prime_oneHundredNineDC_4982579341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 110723210098067601022057) ^ 55361605049033800511028 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 36907736699355867007352 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 2992519191839664892488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 1652585225344292552568 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 1034796356056706551608 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 31719458830518552 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (15 : ZMod 110723210098067601022057) ^ 22222066628616 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_123908042682950595851567 : Nat.Prime 123908042682950595851567 := by
  apply lucas_primality 123908042682950595851567 (5 : ZMod 123908042682950595851567)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (42101, 1), (76223321, 1), (448973561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (42101, 1), (76223321, 1), (448973561, 1)] : List FactorBlock).map factorBlockValue).prod) = 123908042682950595851567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_42101
      · exact prime_oneHundredNineDC_76223321
      · exact prime_oneHundredNineDC_448973561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 123908042682950595851567) ^ 61954021341475297925783 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 123908042682950595851567) ^ 2881582387975595252362 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 123908042682950595851567) ^ 2943114004012982966 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 123908042682950595851567) ^ 1625592286682846 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 123908042682950595851567) ^ 275980711218206 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_137952799708830960487399 : Nat.Prime 137952799708830960487399 := by
  apply lucas_primality 137952799708830960487399 (3 : ZMod 137952799708830960487399)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (587, 1), (11551, 1), (34958263295597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (587, 1), (11551, 1), (34958263295597, 1)] : List FactorBlock).map factorBlockValue).prod) = 137952799708830960487399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_97
      · exact prime_oneHundredNineDC_587
      · exact prime_oneHundredNineDC_11551
      · exact prime_oneHundredNineDC_34958263295597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 137952799708830960487399) ^ 68976399854415480243699 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 137952799708830960487399) ^ 45984266569610320162466 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 137952799708830960487399) ^ 1422193811431247015334 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 137952799708830960487399) ^ 235013287408570631154 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 137952799708830960487399) ^ 11942931322727985498 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 137952799708830960487399) ^ 3946214334 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_164010423961573889845351 : Nat.Prime 164010423961573889845351 := by
  apply lucas_primality 164010423961573889845351 (3 : ZMod 164010423961573889845351)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (199, 1), (1777, 1), (3092001443374703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (199, 1), (1777, 1), (3092001443374703, 1)] : List FactorBlock).map factorBlockValue).prod) = 164010423961573889845351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_199
      · exact prime_oneHundredNineDC_1777
      · exact prime_oneHundredNineDC_3092001443374703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 164010423961573889845351) ^ 82005211980786944922675 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 164010423961573889845351) ^ 54670141320524629948450 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 164010423961573889845351) ^ 32802084792314777969070 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 164010423961573889845351) ^ 824172984731527084650 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 164010423961573889845351) ^ 92296243084734884550 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 164010423961573889845351) ^ 53043450 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_237586380495625274656091 : Nat.Prime 237586380495625274656091 := by
  apply lucas_primality 237586380495625274656091 (2 : ZMod 237586380495625274656091)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23758638049562527465609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23758638049562527465609, 1)] : List FactorBlock).map factorBlockValue).prod) = 237586380495625274656091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_23758638049562527465609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 237586380495625274656091) ^ 118793190247812637328045 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237586380495625274656091) ^ 47517276099125054931218 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 237586380495625274656091) ^ 10 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_246956978205526128930931 : Nat.Prime 246956978205526128930931 := by
  apply lucas_primality 246956978205526128930931 (2 : ZMod 246956978205526128930931)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (5466427, 1), (20628784299661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (5466427, 1), (20628784299661, 1)] : List FactorBlock).map factorBlockValue).prod) = 246956978205526128930931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_5466427
      · exact prime_oneHundredNineDC_20628784299661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 246956978205526128930931) ^ 123478489102763064465465 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 246956978205526128930931) ^ 82318992735175376310310 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 246956978205526128930931) ^ 49391395641105225786186 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 246956978205526128930931) ^ 3382972304185289437410 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 246956978205526128930931) ^ 45177037616257590 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 246956978205526128930931) ^ 11971475130 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_476679959781491085764153 : Nat.Prime 476679959781491085764153 := by
  apply lucas_primality 476679959781491085764153 (3 : ZMod 476679959781491085764153)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (191, 1), (2657, 1), (117411864683600537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (191, 1), (2657, 1), (117411864683600537, 1)] : List FactorBlock).map factorBlockValue).prod) = 476679959781491085764153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_191
      · exact prime_oneHundredNineDC_2657
      · exact prime_oneHundredNineDC_117411864683600537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 476679959781491085764153) ^ 238339979890745542882076 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 476679959781491085764153) ^ 2495706595714613014472 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 476679959781491085764153) ^ 179405329236541620536 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 476679959781491085764153) ^ 4059896 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_484847342693669206019581 : Nat.Prime 484847342693669206019581 := by
  apply lucas_primality 484847342693669206019581 (2 : ZMod 484847342693669206019581)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (79, 1), (523705891, 1), (962150879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (29, 1), (79, 1), (523705891, 1), (962150879, 1)] : List FactorBlock).map factorBlockValue).prod) = 484847342693669206019581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_29
      · exact prime_oneHundredNineDC_79
      · exact prime_oneHundredNineDC_523705891
      · exact prime_oneHundredNineDC_962150879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 484847342693669206019581) ^ 242423671346834603009790 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 161615780897889735339860 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 96969468538733841203916 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 69263906099095600859940 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 16718873885988593311020 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 6137308135362901342020 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 925800818791380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 484847342693669206019581) ^ 503920282438020 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_815289412242002521771309 : Nat.Prime 815289412242002521771309 := by
  apply lucas_primality 815289412242002521771309 (2 : ZMod 815289412242002521771309)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5917540903, 1), (11481253018303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5917540903, 1), (11481253018303, 1)] : List FactorBlock).map factorBlockValue).prod) = 815289412242002521771309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5917540903
      · exact prime_oneHundredNineDC_11481253018303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 815289412242002521771309) ^ 407644706121001260885654 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 815289412242002521771309) ^ 271763137414000840590436 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 815289412242002521771309) ^ 137775036219636 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 815289412242002521771309) ^ 71010490836 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1779538919122951344989207 : Nat.Prime 1779538919122951344989207 := by
  apply lucas_primality 1779538919122951344989207 (5 : ZMod 1779538919122951344989207)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (3121, 1), (42397, 1), (85118019075161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (3121, 1), (42397, 1), (85118019075161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1779538919122951344989207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_79
      · exact prime_oneHundredNineDC_3121
      · exact prime_oneHundredNineDC_42397
      · exact prime_oneHundredNineDC_85118019075161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1779538919122951344989207) ^ 889769459561475672494603 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1779538919122951344989207) ^ 22525809102822168923914 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1779538919122951344989207) ^ 570182287447276944886 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1779538919122951344989207) ^ 41973227330305241998 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 1779538919122951344989207) ^ 20906723846 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_2454517739651968393560977 : Nat.Prime 2454517739651968393560977 := by
  apply lucas_primality 2454517739651968393560977 (5 : ZMod 2454517739651968393560977)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (17, 1), (53, 1), (1447, 1), (1293038565657193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (17, 1), (53, 1), (1447, 1), (1293038565657193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2454517739651968393560977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_17
      · exact prime_oneHundredNineDC_53
      · exact prime_oneHundredNineDC_1447
      · exact prime_oneHundredNineDC_1293038565657193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2454517739651968393560977) ^ 1227258869825984196780488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 350645391378852627651568 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 188809056896305261043152 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 144383396450115787856528 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 46311655465131479123792 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 1696280400588782580208 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 2454517739651968393560977) ^ 1898255632 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_3385626208317989769559373 : Nat.Prime 3385626208317989769559373 := by
  apply lucas_primality 3385626208317989769559373 (2 : ZMod 3385626208317989769559373)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (157, 1), (577, 1), (18493, 1), (26591484342361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (157, 1), (577, 1), (18493, 1), (26591484342361, 1)] : List FactorBlock).map factorBlockValue).prod) = 3385626208317989769559373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_19
      · exact prime_oneHundredNineDC_157
      · exact prime_oneHundredNineDC_577
      · exact prime_oneHundredNineDC_18493
      · exact prime_oneHundredNineDC_26591484342361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3385626208317989769559373) ^ 1692813104158994884779686 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385626208317989769559373) ^ 178190853069367882608388 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385626208317989769559373) ^ 21564498142152801079996 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385626208317989769559373) ^ 5867636409563240501836 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385626208317989769559373) ^ 183076094106850687804 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 3385626208317989769559373) ^ 127319940652 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4865846940311419898759191 : Nat.Prime 4865846940311419898759191 := by
  apply lucas_primality 4865846940311419898759191 (3 : ZMod 4865846940311419898759191)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1737641369, 1), (93341986962317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1737641369, 1), (93341986962317, 1)] : List FactorBlock).map factorBlockValue).prod) = 4865846940311419898759191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_1737641369
      · exact prime_oneHundredNineDC_93341986962317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4865846940311419898759191) ^ 2432923470155709949379595 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4865846940311419898759191) ^ 1621948980103806632919730 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4865846940311419898759191) ^ 973169388062283979751838 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4865846940311419898759191) ^ 2800259608869510 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 4865846940311419898759191) ^ 52129241070 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_5507611349996052850617079 : Nat.Prime 5507611349996052850617079 := by
  apply lucas_primality 5507611349996052850617079 (3 : ZMod 5507611349996052850617079)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (73, 1), (113, 1), (193, 1), (6263, 1), (13151429812849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (73, 1), (113, 1), (193, 1), (6263, 1), (13151429812849, 1)] : List FactorBlock).map factorBlockValue).prod) = 5507611349996052850617079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_73
      · exact prime_oneHundredNineDC_113
      · exact prime_oneHundredNineDC_193
      · exact prime_oneHundredNineDC_6263
      · exact prime_oneHundredNineDC_13151429812849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5507611349996052850617079) ^ 2753805674998026425308539 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 1835870449998684283539026 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 786801621428007550088154 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 75446730821863737679686 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 48739923451292503102806 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 28536846373036543267446 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 879388687529307496506 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 5507611349996052850617079) ^ 418784225622 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_5792299998526053784553147 : Nat.Prime 5792299998526053784553147 := by
  apply lucas_primality 5792299998526053784553147 (2 : ZMod 5792299998526053784553147)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2543, 1), (1138871411428638180211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2543, 1), (1138871411428638180211, 1)] : List FactorBlock).map factorBlockValue).prod) = 5792299998526053784553147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_2543
      · exact prime_oneHundredNineDC_1138871411428638180211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5792299998526053784553147) ^ 2896149999263026892276573 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5792299998526053784553147) ^ 2277742822857276360422 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 5792299998526053784553147) ^ 5086 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_11062502392240333470575879 : Nat.Prime 11062502392240333470575879 := by
  apply lucas_primality 11062502392240333470575879 (11 : ZMod 11062502392240333470575879)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (389, 1), (18637, 1), (762952983087953923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (389, 1), (18637, 1), (762952983087953923, 1)] : List FactorBlock).map factorBlockValue).prod) = 11062502392240333470575879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_389
      · exact prime_oneHundredNineDC_18637
      · exact prime_oneHundredNineDC_762952983087953923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11062502392240333470575879) ^ 5531251196120166735287939 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 11062502392240333470575879) ^ 28438309491620394525902 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 11062502392240333470575879) ^ 593577420842428152094 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 11062502392240333470575879) ^ 14499586 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_12875121427436071995078271 : Nat.Prime 12875121427436071995078271 := by
  apply lucas_primality 12875121427436071995078271 (3 : ZMod 12875121427436071995078271)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (59, 1), (1733, 1), (209189, 1), (6688356382441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (59, 1), (1733, 1), (209189, 1), (6688356382441, 1)] : List FactorBlock).map factorBlockValue).prod) = 12875121427436071995078271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_59
      · exact prime_oneHundredNineDC_1733
      · exact prime_oneHundredNineDC_209189
      · exact prime_oneHundredNineDC_6688356382441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12875121427436071995078271) ^ 6437560713718035997539135 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 4291707142478690665026090 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 2575024285487214399015654 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 218222397075187660933530 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 7429383397251051353190 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 61547793753190043430 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 12875121427436071995078271) ^ 1925005291470 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_15524285070137049102365789 : Nat.Prime 15524285070137049102365789 := by
  apply lucas_primality 15524285070137049102365789 (2 : ZMod 15524285070137049102365789)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (191, 1), (457, 1), (4042121515058747971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (191, 1), (457, 1), (4042121515058747971, 1)] : List FactorBlock).map factorBlockValue).prod) = 15524285070137049102365789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_11
      · exact prime_oneHundredNineDC_191
      · exact prime_oneHundredNineDC_457
      · exact prime_oneHundredNineDC_4042121515058747971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 15524285070137049102365789) ^ 7762142535068524551182894 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15524285070137049102365789) ^ 1411298642739731736578708 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15524285070137049102365789) ^ 81278979424801304200868 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15524285070137049102365789) ^ 33969989212553717948284 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 15524285070137049102365789) ^ 3840628 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_22647994792127881300305521 : Nat.Prime 22647994792127881300305521 := by
  apply lucas_primality 22647994792127881300305521 (3 : ZMod 22647994792127881300305521)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (37, 1), (193, 1), (239, 1), (3407, 1), (26627, 1), (1828472629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (37, 1), (193, 1), (239, 1), (3407, 1), (26627, 1), (1828472629, 1)] : List FactorBlock).map factorBlockValue).prod) = 22647994792127881300305521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_193
      · exact prime_oneHundredNineDC_239
      · exact prime_oneHundredNineDC_3407
      · exact prime_oneHundredNineDC_26627
      · exact prime_oneHundredNineDC_1828472629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 22647994792127881300305521) ^ 11323997396063940650152760 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 4529598958425576260061104 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 612107967354807602710960 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 117347123275273996374640 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 94761484485890716737680 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 6647488932235949897360 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 850565020172301847760 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 22647994792127881300305521) ^ 12386291395848880 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_39217008632747305112214977 : Nat.Prime 39217008632747305112214977 := by
  apply lucas_primality 39217008632747305112214977 (3 : ZMod 39217008632747305112214977)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (12143, 1), (224993, 1), (3702943, 1), (60569287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (12143, 1), (224993, 1), (3702943, 1), (60569287, 1)] : List FactorBlock).map factorBlockValue).prod) = 39217008632747305112214977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_12143
      · exact prime_oneHundredNineDC_224993
      · exact prime_oneHundredNineDC_3702943
      · exact prime_oneHundredNineDC_60569287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 39217008632747305112214977) ^ 19608504316373652556107488 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39217008632747305112214977) ^ 3229598009779074784832 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39217008632747305112214977) ^ 174303238912976426432 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39217008632747305112214977) ^ 10590767568592685632 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 39217008632747305112214977) ^ 647473506378691648 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_41556623788199820896078173 : Nat.Prime 41556623788199820896078173 := by
  apply lucas_primality 41556623788199820896078173 (2 : ZMod 41556623788199820896078173)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (149, 1), (3319, 1), (7002699491740629151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (149, 1), (3319, 1), (7002699491740629151, 1)] : List FactorBlock).map factorBlockValue).prod) = 41556623788199820896078173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_149
      · exact prime_oneHundredNineDC_3319
      · exact prime_oneHundredNineDC_7002699491740629151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41556623788199820896078173) ^ 20778311894099910448039086 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41556623788199820896078173) ^ 13852207929399940298692724 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41556623788199820896078173) ^ 278903515357045777826028 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41556623788199820896078173) ^ 12520826691232244921988 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 41556623788199820896078173) ^ 5934372 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_76706601409052169404010961 : Nat.Prime 76706601409052169404010961 := by
  apply lucas_primality 76706601409052169404010961 (11 : ZMod 76706601409052169404010961)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (8867869, 1), (36041447974071791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (8867869, 1), (36041447974071791, 1)] : List FactorBlock).map factorBlockValue).prod) = 76706601409052169404010961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_8867869
      · exact prime_oneHundredNineDC_36041447974071791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 76706601409052169404010961) ^ 38353300704526084702005480 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76706601409052169404010961) ^ 25568867136350723134670320 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76706601409052169404010961) ^ 15341320281810433880802192 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76706601409052169404010961) ^ 8649947513777229840 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 76706601409052169404010961) ^ 2128288560 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_82080949278476206750788799 : Nat.Prime 82080949278476206750788799 := by
  apply lucas_primality 82080949278476206750788799 (6 : ZMod 82080949278476206750788799)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (24831333557, 1), (42378709147013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (24831333557, 1), (42378709147013, 1)] : List FactorBlock).map factorBlockValue).prod) = 82080949278476206750788799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_24831333557
      · exact prime_oneHundredNineDC_42378709147013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 82080949278476206750788799) ^ 41040474639238103375394399 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82080949278476206750788799) ^ 27360316426158735583596266 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82080949278476206750788799) ^ 6313919175267400519291446 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82080949278476206750788799) ^ 3305539313467014 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (6 : ZMod 82080949278476206750788799) ^ 1936844017446 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_101790750684998139493474261 : Nat.Prime 101790750684998139493474261 := by
  apply lucas_primality 101790750684998139493474261 (7 : ZMod 101790750684998139493474261)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (43, 1), (149, 1), (20011, 1), (46406033, 1), (95046877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (43, 1), (149, 1), (20011, 1), (46406033, 1), (95046877, 1)] : List FactorBlock).map factorBlockValue).prod) = 101790750684998139493474261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_43
      · exact prime_oneHundredNineDC_149
      · exact prime_oneHundredNineDC_20011
      · exact prime_oneHundredNineDC_46406033
      · exact prime_oneHundredNineDC_95046877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 101790750684998139493474261) ^ 50895375342499069746737130 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 33930250228332713164491420 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 20358150136999627898694852 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 2367226760116235802173820 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 683159400570457312036740 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 5086739827344867297660 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 2193480978755459220 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (7 : ZMod 101790750684998139493474261) ^ 1070953132789393380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_441325651942491933557323337 : Nat.Prime 441325651942491933557323337 := by
  apply lucas_primality 441325651942491933557323337 (3 : ZMod 441325651942491933557323337)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (1779538919122951344989207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (1779538919122951344989207, 1)] : List FactorBlock).map factorBlockValue).prod) = 441325651942491933557323337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_31
      · exact prime_oneHundredNineDC_1779538919122951344989207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 441325651942491933557323337) ^ 220662825971245966778661668 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 441325651942491933557323337) ^ 14236311352983610759913656 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 441325651942491933557323337) ^ 248 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_1239106638146227351910946293 : Nat.Prime 1239106638146227351910946293 := by
  apply lucas_primality 1239106638146227351910946293 (2 : ZMod 1239106638146227351910946293)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (571, 1), (77502291602841340499809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (571, 1), (77502291602841340499809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1239106638146227351910946293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_571
      · exact prime_oneHundredNineDC_77502291602841340499809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1239106638146227351910946293) ^ 619553319073113675955473146 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239106638146227351910946293) ^ 177015234020889621701563756 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239106638146227351910946293) ^ 2170064164879557533994652 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 1239106638146227351910946293) ^ 15988 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4027096573975238893710575453 : Nat.Prime 4027096573975238893710575453 := by
  apply lucas_primality 4027096573975238893710575453 (2 : ZMod 4027096573975238893710575453)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (131, 1), (16229, 1), (47279, 1), (3445499, 1), (126392339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (131, 1), (16229, 1), (47279, 1), (3445499, 1), (126392339, 1)] : List FactorBlock).map factorBlockValue).prod) = 4027096573975238893710575453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_23
      · exact prime_oneHundredNineDC_131
      · exact prime_oneHundredNineDC_16229
      · exact prime_oneHundredNineDC_47279
      · exact prime_oneHundredNineDC_3445499
      · exact prime_oneHundredNineDC_126392339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4027096573975238893710575453) ^ 2013548286987619446855287726 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 175091155390227777987416324 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 30741195221185029722981492 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 248142003449087367903788 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 85177279002839292153188 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 1168799228783766558548 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4027096573975238893710575453) ^ 31861872371673087668 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_4443692771283022227542703947 : Nat.Prime 4443692771283022227542703947 := by
  apply lucas_primality 4443692771283022227542703947 (2 : ZMod 4443692771283022227542703947)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (72817, 1), (307033, 1), (44008619, 1), (2258179447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (72817, 1), (307033, 1), (44008619, 1), (2258179447, 1)] : List FactorBlock).map factorBlockValue).prod) = 4443692771283022227542703947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_72817
      · exact prime_oneHundredNineDC_307033
      · exact prime_oneHundredNineDC_44008619
      · exact prime_oneHundredNineDC_2258179447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4443692771283022227542703947) ^ 2221846385641511113771351973 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443692771283022227542703947) ^ 61025485412513866645738 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443692771283022227542703947) ^ 14473013556467943926362 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443692771283022227542703947) ^ 100973238248694471134 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 4443692771283022227542703947) ^ 1967820926360163718 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_8591139357813842973249227633 : Nat.Prime 8591139357813842973249227633 := by
  apply lucas_primality 8591139357813842973249227633 (3 : ZMod 8591139357813842973249227633)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (76706601409052169404010961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (76706601409052169404010961, 1)] : List FactorBlock).map factorBlockValue).prod) = 8591139357813842973249227633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_76706601409052169404010961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8591139357813842973249227633) ^ 4295569678906921486624613816 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8591139357813842973249227633) ^ 1227305622544834710464175376 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (3 : ZMod 8591139357813842973249227633) ^ 112 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_32216772591801911149684603603 : Nat.Prime 32216772591801911149684603603 := by
  apply lucas_primality 32216772591801911149684603603 (2 : ZMod 32216772591801911149684603603)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5051, 1), (33632107, 1), (31608168845812331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5051, 1), (33632107, 1), (31608168845812331, 1)] : List FactorBlock).map factorBlockValue).prod) = 32216772591801911149684603603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5051
      · exact prime_oneHundredNineDC_33632107
      · exact prime_oneHundredNineDC_31608168845812331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32216772591801911149684603603) ^ 16108386295900955574842301801 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32216772591801911149684603603) ^ 10738924197267303716561534534 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32216772591801911149684603603) ^ 6378295900178560908668502 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32216772591801911149684603603) ^ 957917165041188503286 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (2 : ZMod 32216772591801911149684603603) ^ 1019254634742 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_32216772591801911149684603607 : Nat.Prime 32216772591801911149684603607 := by
  apply lucas_primality 32216772591801911149684603607 (5 : ZMod 32216772591801911149684603607)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (3011, 1), (17417, 1), (1185954874480453691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (3011, 1), (17417, 1), (1185954874480453691, 1)] : List FactorBlock).map factorBlockValue).prod) = 32216772591801911149684603607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_37
      · exact prime_oneHundredNineDC_3011
      · exact prime_oneHundredNineDC_17417
      · exact prime_oneHundredNineDC_1185954874480453691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32216772591801911149684603607) ^ 16108386295900955574842301803 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32216772591801911149684603607) ^ 4602396084543130164240657658 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32216772591801911149684603607) ^ 870723583562213814856340638 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32216772591801911149684603607) ^ 10699691993291900082924146 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32216772591801911149684603607) ^ 1849731445817414660945318 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (5 : ZMod 32216772591801911149684603607) ^ 27165260066 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_42955696789069214866246138141 : Nat.Prime 42955696789069214866246138141 := by
  apply lucas_primality 42955696789069214866246138141 (10 : ZMod 42955696789069214866246138141)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (223, 1), (246956978205526128930931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (223, 1), (246956978205526128930931, 1)] : List FactorBlock).map factorBlockValue).prod) = 42955696789069214866246138141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_13
      · exact prime_oneHundredNineDC_223
      · exact prime_oneHundredNineDC_246956978205526128930931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 42955696789069214866246138141) ^ 21477848394534607433123069070 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 42955696789069214866246138141) ^ 14318565596356404955415379380 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 42955696789069214866246138141) ^ 8591139357813842973249227628 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 42955696789069214866246138141) ^ 3304284368389939605095856780 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 42955696789069214866246138141) ^ 192626443000310380566126180 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (10 : ZMod 42955696789069214866246138141) ^ 173940 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem prime_oneHundredNineDC_128867090367207644598738414481 : Nat.Prime 128867090367207644598738414481 := by
  apply lucas_primality 128867090367207644598738414481 (11 : ZMod 128867090367207644598738414481)
  · rw [← oneHundredNineDCFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (76706601409052169404010961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (76706601409052169404010961, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredNineDC_2
      · exact prime_oneHundredNineDC_3
      · exact prime_oneHundredNineDC_5
      · exact prime_oneHundredNineDC_7
      · exact prime_oneHundredNineDC_76706601409052169404010961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 128867090367207644598738414481) ^ 64433545183603822299369207240 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 128867090367207644598738414481) ^ 42955696789069214866246138160 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 128867090367207644598738414481) ^ 25773418073441528919747682896 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 128867090367207644598738414481) ^ 18409584338172520656962630640 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide
    · change (11 : ZMod 128867090367207644598738414481) ^ 1680 ≠ 1
      rw [← oneHundredNineDCFastPow_eq_pow]
      decide

private theorem phi_oneHundredNineDC_128867090367207644598738414400 : Nat.totient 128867090367207644598738414400 = 51073631334074024124291072000 := by
  rw [← show ((([(2, 6), (5, 2), (109, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414400 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_109, prime_oneHundredNineDC_171401, prime_oneHundredNineDC_714027719, prime_oneHundredNineDC_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414401 : Nat.totient 128867090367207644598738414401 = 125886870926999794946377728000 := by
  rw [← show ((([(59, 1), (191, 1), (971, 1), (42737, 1), (3059137, 1), (90081260471, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414401 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_59, prime_oneHundredNineDC_191, prime_oneHundredNineDC_971, prime_oneHundredNineDC_42737, prime_oneHundredNineDC_3059137, prime_oneHundredNineDC_90081260471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414402 : Nat.totient 128867090367207644598738414402 = 42739834544183488227402680640 := by
  rw [← show ((([(2, 1), (3, 3), (199, 1), (10373939, 1), (122954653, 1), (9401703011, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414402 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_199, prime_oneHundredNineDC_10373939, prime_oneHundredNineDC_122954653, prime_oneHundredNineDC_9401703011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414403 : Nat.totient 128867090367207644598738414403 = 110457196794898137810511242000 := by
  rw [← show ((([(7, 2), (357197, 1), (7362717547288839274751, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414403 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_7, prime_oneHundredNineDC_357197, prime_oneHundredNineDC_7362717547288839274751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414404 : Nat.totient 128867090367207644598738414404 = 63550893879718838432254560384 := by
  rw [← show ((([(2, 2), (73, 1), (441325651942491933557323337, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414404 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_73, prime_oneHundredNineDC_441325651942491933557323337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414405 : Nat.totient 128867090367207644598738414405 = 60309313663439810745151084800 := by
  rw [← show ((([(3, 1), (5, 1), (11, 1), (29, 1), (3511, 1), (7670598502167253096403, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414405 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_11, prime_oneHundredNineDC_29, prime_oneHundredNineDC_3511, prime_oneHundredNineDC_7670598502167253096403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414406 : Nat.totient 128867090367207644598738414406 = 63724941209445786255839568000 := by
  rw [← show ((([(2, 1), (101, 1), (1319, 1), (2861, 1), (169054992225574313317, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414406 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_101, prime_oneHundredNineDC_1319, prime_oneHundredNineDC_2861, prime_oneHundredNineDC_169054992225574313317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414407 : Nat.totient 128867090367207644598738414407 = 116184153762131702339280408192 := by
  rw [← show ((([(13, 1), (43, 1), (31379, 1), (36737989, 1), (199975014078583, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414407 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_13, prime_oneHundredNineDC_43, prime_oneHundredNineDC_31379, prime_oneHundredNineDC_36737989, prime_oneHundredNineDC_199975014078583]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414408 : Nat.totient 128867090367207644598738414408 = 42947191117565620722145992000 := by
  rw [← show ((([(2, 3), (3, 1), (5051, 1), (33632107, 1), (31608168845812331, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414408 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_5051, prime_oneHundredNineDC_33632107, prime_oneHundredNineDC_31608168845812331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414409 : Nat.totient 128867090367207644598738414409 = 126911701034124076690861182480 := by
  rw [← show ((([(67, 1), (3967, 1), (484847342693669206019581, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414409 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_67, prime_oneHundredNineDC_3967, prime_oneHundredNineDC_484847342693669206019581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414410 : Nat.totient 128867090367207644598738414410 = 44159138732878458393506688000 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (1861, 1), (575699, 1), (971917, 1), (1767962121901, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414410 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_7, prime_oneHundredNineDC_1861, prime_oneHundredNineDC_575699, prime_oneHundredNineDC_971917, prime_oneHundredNineDC_1767962121901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414411 : Nat.totient 128867090367207644598738414411 = 85797903757355393526590633280 := by
  rw [← show ((([(3, 2), (757, 1), (162066787, 1), (116710414561575181, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414411 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_757, prime_oneHundredNineDC_162066787, prime_oneHundredNineDC_116710414561575181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414412 : Nat.totient 128867090367207644598738414412 = 64433545183603822299369207204 := by
  rw [← show ((([(2, 2), (32216772591801911149684603603, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414412 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_32216772591801911149684603603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414413 : Nat.totient 128867090367207644598738414413 = 128712153533382742393165455360 := by
  rw [← show ((([(1499, 1), (2917, 1), (5693, 1), (61483, 1), (1157729, 1), (72727861, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414413 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_1499, prime_oneHundredNineDC_2917, prime_oneHundredNineDC_5693, prime_oneHundredNineDC_61483, prime_oneHundredNineDC_1157729, prime_oneHundredNineDC_72727861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414414 : Nat.totient 128867090367207644598738414414 = 40340005139629621530585907200 := by
  rw [← show ((([(2, 1), (3, 1), (17, 2), (457, 1), (97829, 1), (5202157, 1), (319540316101, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414414 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_17, prime_oneHundredNineDC_457, prime_oneHundredNineDC_97829, prime_oneHundredNineDC_5202157, prime_oneHundredNineDC_319540316101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414415 : Nat.totient 128867090367207644598738414415 = 102584068594136318257972675200 := by
  rw [← show ((([(5, 1), (227, 1), (1871, 1), (174331, 1), (348094973803951229, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414415 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_227, prime_oneHundredNineDC_1871, prime_oneHundredNineDC_174331, prime_oneHundredNineDC_348094973803951229]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414416 : Nat.totient 128867090367207644598738414416 = 58509612736970669856267235200 := by
  rw [← show ((([(2, 4), (11, 1), (883, 1), (111139529687, 1), (7461052515971, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414416 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_11, prime_oneHundredNineDC_883, prime_oneHundredNineDC_111139529687, prime_oneHundredNineDC_7461052515971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414417 : Nat.totient 128867090367207644598738414417 = 69762577259028340548240837120 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (1200161, 1), (269109864282865450303, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414417 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_7, prime_oneHundredNineDC_19, prime_oneHundredNineDC_1200161, prime_oneHundredNineDC_269109864282865450303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414418 : Nat.totient 128867090367207644598738414418 = 61594589551220167322040652800 := by
  rw [← show ((([(2, 1), (23, 1), (1741, 1), (35083, 1), (325999, 1), (405521, 1), (346943759, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414418 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_23, prime_oneHundredNineDC_1741, prime_oneHundredNineDC_35083, prime_oneHundredNineDC_325999, prime_oneHundredNineDC_405521, prime_oneHundredNineDC_346943759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414419 : Nat.totient 128867090367207644598738414419 = 125719561673749876904483264640 := by
  rw [← show ((([(41, 1), (28387, 1), (110723210098067601022057, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414419 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_41, prime_oneHundredNineDC_28387, prime_oneHundredNineDC_110723210098067601022057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414420 : Nat.totient 128867090367207644598738414420 = 31578882717097037158655880960 := by
  rw [← show ((([(2, 2), (3, 2), (5, 1), (13, 1), (223, 1), (246956978205526128930931, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414420 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_13, prime_oneHundredNineDC_223, prime_oneHundredNineDC_246956978205526128930931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414421 : Nat.totient 128867090367207644598738414421 = 128867090367010009773189271072 := by
  rw [← show ((([(652048621373, 1), (197634173500521977, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414421 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_652048621373, prime_oneHundredNineDC_197634173500521977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414422 : Nat.totient 128867090367207644598738414422 = 61178533467085795975055362560 := by
  rw [← show ((([(2, 1), (31, 1), (53, 1), (39217008632747305112214977, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414422 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_31, prime_oneHundredNineDC_53, prime_oneHundredNineDC_39217008632747305112214977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414423 : Nat.totient 128867090367207644598738414423 = 85911393578138429732492276280 := by
  rw [← show ((([(3, 1), (42955696789069214866246138141, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414423 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_42955696789069214866246138141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414424 : Nat.totient 128867090367207644598738414424 = 53715153181934240821241625600 := by
  rw [← show ((([(2, 3), (7, 1), (37, 1), (3011, 1), (17417, 1), (1185954874480453691, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414424 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_7, prime_oneHundredNineDC_37, prime_oneHundredNineDC_3011, prime_oneHundredNineDC_17417, prime_oneHundredNineDC_1185954874480453691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414425 : Nat.totient 128867090367207644598738414425 = 103089871871938898506614637440 := by
  rw [← show ((([(5, 2), (27127, 1), (7547917183, 1), (25175211074297, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414425 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_27127, prime_oneHundredNineDC_7547917183, prime_oneHundredNineDC_25175211074297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414426 : Nat.totient 128867090367207644598738414426 = 42752115287699218587259189200 := by
  rw [← show ((([(2, 1), (3, 1), (211, 1), (101790750684998139493474261, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414426 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_211, prime_oneHundredNineDC_101790750684998139493474261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414427 : Nat.totient 128867090367207644598738414427 = 117151895764124585183845995360 := by
  rw [← show ((([(11, 1), (25636669, 1), (456970054626929619653, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414427 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_11, prime_oneHundredNineDC_25636669, prime_oneHundredNineDC_456970054626929619653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414428 : Nat.totient 128867090367207644598738414428 = 64433545183603822299369207212 := by
  rw [← show ((([(2, 2), (32216772591801911149684603607, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414428 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_32216772591801911149684603607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414429 : Nat.totient 128867090367207644598738414429 = 85431440036203718746691248128 := by
  rw [← show ((([(3, 4), (179, 1), (52654079, 1), (168799809564238849, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414429 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_179, prime_oneHundredNineDC_52654079, prime_oneHundredNineDC_168799809564238849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414430 : Nat.totient 128867090367207644598738414430 = 51218512349769153012492209952 := by
  rw [← show ((([(2, 1), (5, 1), (157, 1), (82080949278476206750788799, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414430 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_157, prime_oneHundredNineDC_82080949278476206750788799]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414431 : Nat.totient 128867090367207644598738414431 = 103960004945572360557701276544 := by
  rw [← show ((([(7, 1), (17, 1), (142642783, 1), (7591808733673221703, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414431 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_7, prime_oneHundredNineDC_17, prime_oneHundredNineDC_142642783, prime_oneHundredNineDC_7591808733673221703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414432 : Nat.totient 128867090367207644598738414432 = 42512854553511020983355572224 := by
  rw [← show ((([(2, 5), (3, 1), (97, 1), (68666021777, 1), (201538104053593, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414432 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_97, prime_oneHundredNineDC_68666021777, prime_oneHundredNineDC_201538104053593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414433 : Nat.totient 128867090367207644598738414433 = 118932194492803150371704114496 := by
  rw [← show ((([(13, 1), (6299, 1), (37699, 1), (36270467, 1), (1150917210823, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414433 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_13, prime_oneHundredNineDC_6299, prime_oneHundredNineDC_37699, prime_oneHundredNineDC_36270467, prime_oneHundredNineDC_1150917210823]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414434 : Nat.totient 128867090367207644598738414434 = 62210640380609025212513937408 := by
  rw [← show ((([(2, 1), (29, 1), (72817, 1), (307033, 1), (44008619, 1), (2258179447, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414434 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_29, prime_oneHundredNineDC_72817, prime_oneHundredNineDC_307033, prime_oneHundredNineDC_44008619, prime_oneHundredNineDC_2258179447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414435 : Nat.totient 128867090367207644598738414435 = 67673042035777606630802374656 := by
  rw [← show ((([(3, 1), (5, 1), (113, 1), (167, 1), (2087, 1), (9029, 1), (24159822937935913, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414435 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_113, prime_oneHundredNineDC_167, prime_oneHundredNineDC_2087, prime_oneHundredNineDC_9029, prime_oneHundredNineDC_24159822937935913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414436 : Nat.totient 128867090367207644598738414436 = 59722361483864221217255731200 := by
  rw [← show ((([(2, 2), (19, 1), (47, 1), (4721, 1), (7013, 1), (1089664326928454681, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414436 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_19, prime_oneHundredNineDC_47, prime_oneHundredNineDC_4721, prime_oneHundredNineDC_7013, prime_oneHundredNineDC_1089664326928454681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414437 : Nat.totient 128867090367207644598738414437 = 128867087064124700777965350960 := by
  rw [← show ((([(39373303, 1), (4301660639, 1), (760858730461, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414437 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_39373303, prime_oneHundredNineDC_4301660639, prime_oneHundredNineDC_760858730461]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414438 : Nat.totient 128867090367207644598738414438 = 33471971523648443645782418880 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (11, 1), (110998284707, 1), (837649869302669, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414438 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_7, prime_oneHundredNineDC_11, prime_oneHundredNineDC_110998284707, prime_oneHundredNineDC_837649869302669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414439 : Nat.totient 128867090367207644598738414439 = 128854215245780208526743326160 := by
  rw [← show ((([(10009, 1), (12875121427436071995078271, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414439 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_10009, prime_oneHundredNineDC_12875121427436071995078271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414440 : Nat.totient 128867090367207644598738414440 = 51415679040251267451048202240 := by
  rw [← show ((([(2, 3), (5, 1), (653, 1), (1061, 1), (16823, 1), (78707, 1), (3511855696997, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414440 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_653, prime_oneHundredNineDC_1061, prime_oneHundredNineDC_16823, prime_oneHundredNineDC_78707, prime_oneHundredNineDC_3511855696997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414441 : Nat.totient 128867090367207644598738414441 = 82169507965226640699517920000 := by
  rw [← show ((([(3, 1), (23, 1), (16699, 1), (48751, 1), (76084213, 1), (30152573597, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414441 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_23, prime_oneHundredNineDC_16699, prime_oneHundredNineDC_48751, prime_oneHundredNineDC_76084213, prime_oneHundredNineDC_30152573597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414442 : Nat.totient 128867090367207644598738414442 = 64428037572253826246518578444 := by
  rw [← show ((([(2, 1), (11699, 1), (5507611349996052850617079, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414442 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_11699, prime_oneHundredNineDC_5507611349996052850617079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414443 : Nat.totient 128867090367207644598738414443 = 128703863564246918765561932800 := by
  rw [← show ((([(797, 1), (122051, 1), (266977, 1), (4962134260473197, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414443 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_797, prime_oneHundredNineDC_122051, prime_oneHundredNineDC_266977, prime_oneHundredNineDC_4962134260473197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414444 : Nat.totient 128867090367207644598738414444 = 42936233401307969186651092560 := by
  rw [← show ((([(2, 2), (3, 1), (2207, 1), (4865846940311419898759191, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414444 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_2207, prime_oneHundredNineDC_4865846940311419898759191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414445 : Nat.totient 128867090367207644598738414445 = 86903278697153272754112560640 := by
  rw [← show ((([(5, 1), (7, 1), (61, 1), (6163, 1), (9793816795723032830489, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414445 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_7, prime_oneHundredNineDC_61, prime_oneHundredNineDC_6163, prime_oneHundredNineDC_9793816795723032830489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414446 : Nat.totient 128867090367207644598738414446 = 59466263053605820737253964640 := by
  rw [← show ((([(2, 1), (13, 1), (5479, 1), (552215779, 1), (1638168468925831, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414446 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_13, prime_oneHundredNineDC_5479, prime_oneHundredNineDC_552215779, prime_oneHundredNineDC_1638168468925831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414447 : Nat.totient 128867090367207644598738414447 = 84945365330501949087369050496 := by
  rw [← show ((([(3, 2), (89, 1), (116923, 1), (16406867, 1), (83865607902767, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414447 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_89, prime_oneHundredNineDC_116923, prime_oneHundredNineDC_16406867, prime_oneHundredNineDC_83865607902767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414448 : Nat.totient 128867090367207644598738414448 = 59789205115749146026671897600 := by
  rw [← show ((([(2, 4), (17, 1), (71, 1), (2333413699, 1), (2859716801348971, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414448 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_17, prime_oneHundredNineDC_71, prime_oneHundredNineDC_2333413699, prime_oneHundredNineDC_2859716801348971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414449 : Nat.totient 128867090367207644598738414449 = 115715503713761442505614032400 := by
  rw [← show ((([(11, 1), (83, 1), (4643, 1), (30399928466956379847211, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414449 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_11, prime_oneHundredNineDC_83, prime_oneHundredNineDC_4643, prime_oneHundredNineDC_30399928466956379847211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414450 : Nat.totient 128867090367207644598738414450 = 33542809049900943946220256000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 2), (43, 1), (1487, 1), (434186293, 1), (30945338012851, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414450 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_43, prime_oneHundredNineDC_1487, prime_oneHundredNineDC_434186293, prime_oneHundredNineDC_30945338012851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414451 : Nat.totient 128867090367207644598738414451 = 128507922183805160159256807168 := by
  rw [← show ((([(503, 1), (1249, 1), (1380445519, 1), (148590939321707, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414451 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_503, prime_oneHundredNineDC_1249, prime_oneHundredNineDC_1380445519, prime_oneHundredNineDC_148590939321707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414452 : Nat.totient 128867090367207644598738414452 = 55228041679617000185716690560 := by
  rw [← show ((([(2, 2), (7, 2), (77641, 1), (8468272625735537674757, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414452 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_7, prime_oneHundredNineDC_77641, prime_oneHundredNineDC_8468272625735537674757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414453 : Nat.totient 128867090367207644598738414453 = 83140055565688399948481940480 := by
  rw [← show ((([(3, 1), (31, 1), (30897029, 1), (2022312337, 1), (22176557077, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414453 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_31, prime_oneHundredNineDC_30897029, prime_oneHundredNineDC_2022312337, prime_oneHundredNineDC_22176557077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414454 : Nat.totient 128867090367207644598738414454 = 64431090665864170330975620000 := by
  rw [← show ((([(2, 1), (26251, 1), (2454517739651968393560977, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414454 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_26251, prime_oneHundredNineDC_2454517739651968393560977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414455 : Nat.totient 128867090367207644598738414455 = 96431261495029077409169614848 := by
  rw [← show ((([(5, 1), (19, 1), (79, 1), (761417, 1), (62974537, 1), (358099549079, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414455 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_19, prime_oneHundredNineDC_79, prime_oneHundredNineDC_761417, prime_oneHundredNineDC_62974537, prime_oneHundredNineDC_358099549079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414456 : Nat.totient 128867090367207644598738414456 = 42538651189175338993758304224 := by
  rw [← show ((([(2, 3), (3, 3), (103, 1), (5792299998526053784553147, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414456 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_103, prime_oneHundredNineDC_5792299998526053784553147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414457 : Nat.totient 128867090367207644598738414457 = 128467468442290503851895799344 := by
  rw [← show ((([(347, 1), (4549, 1), (81638799778782583624319, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414457 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_347, prime_oneHundredNineDC_4549, prime_oneHundredNineDC_81638799778782583624319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414458 : Nat.totient 128867090367207644598738414458 = 64400083336582979724289647360 := by
  rw [← show ((([(2, 1), (2069, 1), (27823, 1), (13507447, 1), (82865605606961, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414458 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_2069, prime_oneHundredNineDC_27823, prime_oneHundredNineDC_13507447, prime_oneHundredNineDC_82865605606961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414459 : Nat.totient 128867090367207644598738414459 = 67519619270584321662952704000 := by
  rw [← show ((([(3, 1), (7, 1), (13, 1), (151, 1), (19919, 1), (98897, 1), (1586908108739731, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414459 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_7, prime_oneHundredNineDC_13, prime_oneHundredNineDC_151, prime_oneHundredNineDC_19919, prime_oneHundredNineDC_98897, prime_oneHundredNineDC_1586908108739731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414460 : Nat.totient 128867090367207644598738414460 = 44576416610848841962586112000 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (41, 1), (59, 1), (127, 1), (6661, 1), (9173, 1), (41113, 1), (759013949, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414460 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_11, prime_oneHundredNineDC_41, prime_oneHundredNineDC_59, prime_oneHundredNineDC_127, prime_oneHundredNineDC_6661, prime_oneHundredNineDC_9173, prime_oneHundredNineDC_41113, prime_oneHundredNineDC_759013949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414461 : Nat.totient 128867090367207644598738414461 = 125379229732169271424734596688 := by
  rw [← show ((([(37, 1), (25247, 1), (137952799708830960487399, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414461 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_37, prime_oneHundredNineDC_25247, prime_oneHundredNineDC_137952799708830960487399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414462 : Nat.totient 128867090367207644598738414462 = 42816282500887972210916386560 := by
  rw [← show ((([(2, 1), (3, 1), (311, 1), (33113, 1), (26715641263, 1), (78066777253, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414462 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_311, prime_oneHundredNineDC_33113, prime_oneHundredNineDC_26715641263, prime_oneHundredNineDC_78066777253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414463 : Nat.totient 128867090367207644598738414463 = 124423397595924622371195710488 := by
  rw [← show ((([(29, 1), (4443692771283022227542703947, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414463 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_29, prime_oneHundredNineDC_4443692771283022227542703947]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414464 : Nat.totient 128867090367207644598738414464 = 61156532305744244066922864640 := by
  rw [← show ((([(2, 7), (23, 1), (131, 1), (16229, 1), (47279, 1), (3445499, 1), (126392339, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414464 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_23, prime_oneHundredNineDC_131, prime_oneHundredNineDC_16229, prime_oneHundredNineDC_47279, prime_oneHundredNineDC_3445499, prime_oneHundredNineDC_126392339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414465 : Nat.totient 128867090367207644598738414465 = 64653060433067959817585295360 := by
  rw [← show ((([(3, 2), (5, 1), (17, 1), (2713, 1), (8353, 1), (42841, 1), (903883, 1), (191962543, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414465 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_17, prime_oneHundredNineDC_2713, prime_oneHundredNineDC_8353, prime_oneHundredNineDC_42841, prime_oneHundredNineDC_903883, prime_oneHundredNineDC_191962543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414466 : Nat.totient 128867090367207644598738414466 = 55228753014481841901154287840 := by
  rw [← show ((([(2, 1), (7, 1), (1546556444249, 1), (5951798399156431, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414466 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_7, prime_oneHundredNineDC_1546556444249, prime_oneHundredNineDC_5951798399156431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414467 : Nat.totient 128867090367207644598738414467 = 128163495604442796422449617600 := by
  rw [← show ((([(263, 1), (601, 1), (815289412242002521771309, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414467 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_263, prime_oneHundredNineDC_601, prime_oneHundredNineDC_815289412242002521771309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414468 : Nat.totient 128867090367207644598738414468 = 42955696789067684900448316224 := by
  rw [← show ((([(2, 2), (3, 1), (30509907221587, 1), (351981542233897, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414468 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_30509907221587, prime_oneHundredNineDC_351981542233897]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414469 : Nat.totient 128867090367207644598738414469 = 128563390943903790905979070080 := by
  rw [← show ((([(647, 1), (1231, 1), (34768398953, 1), (4653663715189, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414469 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_647, prime_oneHundredNineDC_1231, prime_oneHundredNineDC_34768398953, prime_oneHundredNineDC_4653663715189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414470 : Nat.totient 128867090367207644598738414470 = 51545420963900827887555021312 := by
  rw [← show ((([(2, 1), (5, 1), (44273, 1), (205453, 1), (1416741397767459763, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414470 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_44273, prime_oneHundredNineDC_205453, prime_oneHundredNineDC_1416741397767459763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414471 : Nat.totient 128867090367207644598738414471 = 77880016841371947632854181120 := by
  rw [← show ((([(3, 1), (11, 1), (353, 1), (11062502392240333470575879, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414471 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_11, prime_oneHundredNineDC_353, prime_oneHundredNineDC_11062502392240333470575879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414472 : Nat.totient 128867090367207644598738414472 = 59477118631018912891725422016 := by
  rw [← show ((([(2, 3), (13, 1), (1239106638146227351910946293, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414472 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_13, prime_oneHundredNineDC_1239106638146227351910946293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414473 : Nat.totient 128867090367207644598738414473 = 110208166286305925016399312144 := by
  rw [← show ((([(7, 1), (443, 1), (41556623788199820896078173, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414473 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_7, prime_oneHundredNineDC_443, prime_oneHundredNineDC_41556623788199820896078173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414474 : Nat.totient 128867090367207644598738414474 = 40681488573666339629986149120 := by
  rw [← show ((([(2, 1), (3, 2), (19, 1), (3041, 1), (123908042682950595851567, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414474 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_19, prime_oneHundredNineDC_3041, prime_oneHundredNineDC_123908042682950595851567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414475 : Nat.totient 128867090367207644598738414475 = 100977937824661812499985088000 := by
  rw [← show ((([(5, 2), (53, 1), (593, 1), (164010423961573889845351, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414475 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_53, prime_oneHundredNineDC_593, prime_oneHundredNineDC_164010423961573889845351]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414476 : Nat.totient 128867090367207644598738414476 = 63471850224297332202212957712 := by
  rw [← show ((([(2, 2), (67, 1), (248837399, 1), (1932375736319468743, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414476 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_67, prime_oneHundredNineDC_248837399, prime_oneHundredNineDC_1932375736319468743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414477 : Nat.totient 128867090367207644598738414477 = 84730638082709405758494362112 := by
  rw [← show ((([(3, 1), (73, 1), (21799, 1), (11966810789, 1), (2255708169053, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414477 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_73, prime_oneHundredNineDC_21799, prime_oneHundredNineDC_11966810789, prime_oneHundredNineDC_2255708169053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414478 : Nat.totient 128867090367207644598738414478 = 64433492566622461712142925056 := by
  rw [← show ((([(2, 1), (1224577, 1), (52616981360587225057607, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414478 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_1224577, prime_oneHundredNineDC_52616981360587225057607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414479 : Nat.totient 128867090367207644598738414479 = 128866613687247863107652379984 := by
  rw [← show ((([(270343, 1), (476679959781491085764153, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414479 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_270343, prime_oneHundredNineDC_476679959781491085764153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414480 : Nat.totient 128867090367207644598738414480 = 29455334941076033051140208640 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (7, 1), (76706601409052169404010961, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414480 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_7, prime_oneHundredNineDC_76706601409052169404010961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414481 : Nat.totient 128867090367207644598738414481 = 128867090367207644598738414480 := by
  rw [← show ((([(128867090367207644598738414481, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414481 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_128867090367207644598738414481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414482 : Nat.totient 128867090367207644598738414482 = 55130303085640797319355904000 := by
  rw [← show ((([(2, 1), (11, 1), (17, 1), (23396081, 1), (92334733, 1), (159500557991, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414482 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_11, prime_oneHundredNineDC_17, prime_oneHundredNineDC_23396081, prime_oneHundredNineDC_92334733, prime_oneHundredNineDC_159500557991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414483 : Nat.totient 128867090367207644598738414483 = 84083489693153027764468884000 := by
  rw [← show ((([(3, 3), (47, 1), (53304631, 1), (276269347, 1), (6895769851, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414483 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_47, prime_oneHundredNineDC_53304631, prime_oneHundredNineDC_276269347, prime_oneHundredNineDC_6895769851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414484 : Nat.totient 128867090367207644598738414484 = 62351768798379316403667900000 := by
  rw [← show ((([(2, 2), (31, 1), (19051, 1), (33363511, 1), (1635049154787031, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414484 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_31, prime_oneHundredNineDC_19051, prime_oneHundredNineDC_33363511, prime_oneHundredNineDC_1635049154787031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414485 : Nat.totient 128867090367207644598738414485 = 94740562972309552165992960000 := by
  rw [← show ((([(5, 1), (13, 1), (229, 1), (22111, 1), (34421, 1), (414461, 1), (27445910671, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414485 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_5, prime_oneHundredNineDC_13, prime_oneHundredNineDC_229, prime_oneHundredNineDC_22111, prime_oneHundredNineDC_34421, prime_oneHundredNineDC_414461, prime_oneHundredNineDC_27445910671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414486 : Nat.totient 128867090367207644598738414486 = 42945176922224114312858603520 := by
  rw [← show ((([(2, 1), (3, 1), (5059, 1), (21713, 1), (842531, 1), (232070731675553, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414486 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_5059, prime_oneHundredNineDC_21713, prime_oneHundredNineDC_842531, prime_oneHundredNineDC_232070731675553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414487 : Nat.totient 128867090367207644598738414487 = 105655005761996101569492296160 := by
  rw [← show ((([(7, 1), (23, 1), (21531233981, 1), (37174678936731907, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414487 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_7, prime_oneHundredNineDC_23, prime_oneHundredNineDC_21531233981, prime_oneHundredNineDC_37174678936731907]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414488 : Nat.totient 128867090367207644598738414488 = 64037163815166657445436419200 := by
  rw [← show ((([(2, 3), (163, 1), (59611, 1), (6903341, 1), (240147847125647, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414488 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_163, prime_oneHundredNineDC_59611, prime_oneHundredNineDC_6903341, prime_oneHundredNineDC_240147847125647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414489 : Nat.totient 128867090367207644598738414489 = 85880345007998155634287539216 := by
  rw [← show ((([(3, 1), (2767, 1), (15524285070137049102365789, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414489 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_2767, prime_oneHundredNineDC_15524285070137049102365789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414490 : Nat.totient 128867090367207644598738414490 = 51456244167714546314294141440 := by
  rw [← show ((([(2, 1), (5, 1), (569, 1), (22647994792127881300305521, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414490 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_569, prime_oneHundredNineDC_22647994792127881300305521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414491 : Nat.totient 128867090367207644598738414491 = 128866852780827148973463216000 := by
  rw [← show ((([(542401, 1), (237586380495625274656091, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414491 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_542401, prime_oneHundredNineDC_237586380495625274656091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414492 : Nat.totient 128867090367207644598738414492 = 41367698618672008693763993088 := by
  rw [← show ((([(2, 2), (3, 2), (29, 1), (389, 1), (277483, 1), (1143551009668998589, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414492 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_29, prime_oneHundredNineDC_389, prime_oneHundredNineDC_277483, prime_oneHundredNineDC_1143551009668998589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414493 : Nat.totient 128867090367207644598738414493 = 108357169857085574437762632960 := by
  rw [← show ((([(11, 2), (19, 1), (43, 1), (2287, 1), (292489, 1), (1948762409580643, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414493 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_11, prime_oneHundredNineDC_19, prime_oneHundredNineDC_43, prime_oneHundredNineDC_2287, prime_oneHundredNineDC_292489, prime_oneHundredNineDC_1948762409580643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414494 : Nat.totient 128867090367207644598738414494 = 55157434278385236324826047840 := by
  rw [← show ((([(2, 1), (7, 1), (1021, 1), (3203, 1), (2814694771975911517967, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414494 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_7, prime_oneHundredNineDC_1021, prime_oneHundredNineDC_3203, prime_oneHundredNineDC_2814694771975911517967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414495 : Nat.totient 128867090367207644598738414495 = 68729114862510743785993821056 := by
  rw [← show ((([(3, 1), (5, 1), (8591139357813842973249227633, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414495 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_5, prime_oneHundredNineDC_8591139357813842973249227633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414496 : Nat.totient 128867090367207644598738414496 = 64433545183603822299369207232 := by
  rw [← show ((([(2, 5), (4027096573975238893710575453, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414496 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_4027096573975238893710575453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414497 : Nat.totient 128867090367207644598738414497 = 128776393350089205767309726800 := by
  rw [← show ((([(1427, 1), (329591, 1), (273995042908487573021, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414497 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_1427, prime_oneHundredNineDC_329591, prime_oneHundredNineDC_273995042908487573021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414498 : Nat.totient 128867090367207644598738414498 = 38218390944902567006722283520 := by
  rw [← show ((([(2, 1), (3, 1), (13, 2), (37, 1), (107, 1), (47581, 1), (674660060404299833, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414498 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_3, prime_oneHundredNineDC_13, prime_oneHundredNineDC_37, prime_oneHundredNineDC_107, prime_oneHundredNineDC_47581, prime_oneHundredNineDC_674660060404299833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414499 : Nat.totient 128867090367207644598738414499 = 121232503267450577668381992576 := by
  rw [← show ((([(17, 1), (2239, 1), (3385626208317989769559373, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414499 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_17, prime_oneHundredNineDC_2239, prime_oneHundredNineDC_3385626208317989769559373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414500 : Nat.totient 128867090367207644598738414500 = 51544004402713230962828208000 := by
  rw [← show ((([(2, 2), (5, 3), (18211, 1), (42556603, 1), (332560963881613, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414500 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_2, prime_oneHundredNineDC_5, prime_oneHundredNineDC_18211, prime_oneHundredNineDC_42556603, prime_oneHundredNineDC_332560963881613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredNineDC_128867090367207644598738414501 : Nat.totient 128867090367207644598738414501 = 71283303484141904368754688000 := by
  rw [← show ((([(3, 2), (7, 2), (41, 1), (149, 1), (929, 1), (51489371927641184401, 1)] : List FactorBlock).map factorBlockValue).prod) = 128867090367207644598738414501 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredNineDC_3, prime_oneHundredNineDC_7, prime_oneHundredNineDC_41, prime_oneHundredNineDC_149, prime_oneHundredNineDC_929, prime_oneHundredNineDC_51489371927641184401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredNineDC : certifiedKill 1 128867090367207644598738414399 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredNineDC_128867090367207644598738414400, phi_oneHundredNineDC_128867090367207644598738414401, phi_oneHundredNineDC_128867090367207644598738414402,
    phi_oneHundredNineDC_128867090367207644598738414403, phi_oneHundredNineDC_128867090367207644598738414404, phi_oneHundredNineDC_128867090367207644598738414405,
    phi_oneHundredNineDC_128867090367207644598738414406, phi_oneHundredNineDC_128867090367207644598738414407, phi_oneHundredNineDC_128867090367207644598738414408,
    phi_oneHundredNineDC_128867090367207644598738414409, phi_oneHundredNineDC_128867090367207644598738414410, phi_oneHundredNineDC_128867090367207644598738414411,
    phi_oneHundredNineDC_128867090367207644598738414412, phi_oneHundredNineDC_128867090367207644598738414413, phi_oneHundredNineDC_128867090367207644598738414414,
    phi_oneHundredNineDC_128867090367207644598738414415, phi_oneHundredNineDC_128867090367207644598738414416, phi_oneHundredNineDC_128867090367207644598738414417,
    phi_oneHundredNineDC_128867090367207644598738414418, phi_oneHundredNineDC_128867090367207644598738414419, phi_oneHundredNineDC_128867090367207644598738414420,
    phi_oneHundredNineDC_128867090367207644598738414421, phi_oneHundredNineDC_128867090367207644598738414422, phi_oneHundredNineDC_128867090367207644598738414423,
    phi_oneHundredNineDC_128867090367207644598738414424, phi_oneHundredNineDC_128867090367207644598738414425, phi_oneHundredNineDC_128867090367207644598738414426,
    phi_oneHundredNineDC_128867090367207644598738414427, phi_oneHundredNineDC_128867090367207644598738414428, phi_oneHundredNineDC_128867090367207644598738414429,
    phi_oneHundredNineDC_128867090367207644598738414430, phi_oneHundredNineDC_128867090367207644598738414431, phi_oneHundredNineDC_128867090367207644598738414432,
    phi_oneHundredNineDC_128867090367207644598738414433, phi_oneHundredNineDC_128867090367207644598738414434, phi_oneHundredNineDC_128867090367207644598738414435,
    phi_oneHundredNineDC_128867090367207644598738414436, phi_oneHundredNineDC_128867090367207644598738414437, phi_oneHundredNineDC_128867090367207644598738414438,
    phi_oneHundredNineDC_128867090367207644598738414439, phi_oneHundredNineDC_128867090367207644598738414440, phi_oneHundredNineDC_128867090367207644598738414441,
    phi_oneHundredNineDC_128867090367207644598738414442, phi_oneHundredNineDC_128867090367207644598738414443, phi_oneHundredNineDC_128867090367207644598738414444,
    phi_oneHundredNineDC_128867090367207644598738414445, phi_oneHundredNineDC_128867090367207644598738414446, phi_oneHundredNineDC_128867090367207644598738414447,
    phi_oneHundredNineDC_128867090367207644598738414448, phi_oneHundredNineDC_128867090367207644598738414449, phi_oneHundredNineDC_128867090367207644598738414450,
    phi_oneHundredNineDC_128867090367207644598738414451, phi_oneHundredNineDC_128867090367207644598738414452, phi_oneHundredNineDC_128867090367207644598738414453,
    phi_oneHundredNineDC_128867090367207644598738414454, phi_oneHundredNineDC_128867090367207644598738414455, phi_oneHundredNineDC_128867090367207644598738414456,
    phi_oneHundredNineDC_128867090367207644598738414457, phi_oneHundredNineDC_128867090367207644598738414458, phi_oneHundredNineDC_128867090367207644598738414459,
    phi_oneHundredNineDC_128867090367207644598738414460, phi_oneHundredNineDC_128867090367207644598738414461, phi_oneHundredNineDC_128867090367207644598738414462,
    phi_oneHundredNineDC_128867090367207644598738414463, phi_oneHundredNineDC_128867090367207644598738414464, phi_oneHundredNineDC_128867090367207644598738414465,
    phi_oneHundredNineDC_128867090367207644598738414466, phi_oneHundredNineDC_128867090367207644598738414467, phi_oneHundredNineDC_128867090367207644598738414468,
    phi_oneHundredNineDC_128867090367207644598738414469, phi_oneHundredNineDC_128867090367207644598738414470, phi_oneHundredNineDC_128867090367207644598738414471,
    phi_oneHundredNineDC_128867090367207644598738414472, phi_oneHundredNineDC_128867090367207644598738414473, phi_oneHundredNineDC_128867090367207644598738414474,
    phi_oneHundredNineDC_128867090367207644598738414475, phi_oneHundredNineDC_128867090367207644598738414476, phi_oneHundredNineDC_128867090367207644598738414477,
    phi_oneHundredNineDC_128867090367207644598738414478, phi_oneHundredNineDC_128867090367207644598738414479, phi_oneHundredNineDC_128867090367207644598738414480,
    phi_oneHundredNineDC_128867090367207644598738414481, phi_oneHundredNineDC_128867090367207644598738414482, phi_oneHundredNineDC_128867090367207644598738414483,
    phi_oneHundredNineDC_128867090367207644598738414484, phi_oneHundredNineDC_128867090367207644598738414485, phi_oneHundredNineDC_128867090367207644598738414486,
    phi_oneHundredNineDC_128867090367207644598738414487, phi_oneHundredNineDC_128867090367207644598738414488, phi_oneHundredNineDC_128867090367207644598738414489,
    phi_oneHundredNineDC_128867090367207644598738414490, phi_oneHundredNineDC_128867090367207644598738414491, phi_oneHundredNineDC_128867090367207644598738414492,
    phi_oneHundredNineDC_128867090367207644598738414493, phi_oneHundredNineDC_128867090367207644598738414494, phi_oneHundredNineDC_128867090367207644598738414495,
    phi_oneHundredNineDC_128867090367207644598738414496, phi_oneHundredNineDC_128867090367207644598738414497, phi_oneHundredNineDC_128867090367207644598738414498,
    phi_oneHundredNineDC_128867090367207644598738414499, phi_oneHundredNineDC_128867090367207644598738414500, phi_oneHundredNineDC_128867090367207644598738414501
    ]

end TotientTailPeriodKiller
end Erdos249257
