import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtySevenEEFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtySevenEEFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtySevenEEFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtySevenEEFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtySevenEEFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtySevenEEFastPow a n * oneHundredThirtySevenEEFastPow a n * a else oneHundredThirtySevenEEFastPow a n * oneHundredThirtySevenEEFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtySevenEE_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtySevenEE_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtySevenEE_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtySevenEE_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtySevenEE_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtySevenEE_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtySevenEE_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtySevenEE_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtySevenEE_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtySevenEE_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtySevenEE_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtySevenEE_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtySevenEE_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtySevenEE_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtySevenEE_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtySevenEE_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtySevenEE_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtySevenEE_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtySevenEE_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtySevenEE_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtySevenEE_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtySevenEE_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtySevenEE_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtySevenEE_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtySevenEE_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtySevenEE_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtySevenEE_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtySevenEE_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtySevenEE_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtySevenEE_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtySevenEE_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtySevenEE_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtySevenEE_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtySevenEE_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtySevenEE_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtySevenEE_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtySevenEE_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtySevenEE_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtySevenEE_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtySevenEE_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtySevenEE_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtySevenEE_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtySevenEE_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtySevenEE_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtySevenEE_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtySevenEE_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtySevenEE_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtySevenEE_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtySevenEE_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtySevenEE_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtySevenEE_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtySevenEE_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtySevenEE_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtySevenEE_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtySevenEE_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtySevenEE_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtySevenEE_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtySevenEE_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirtySevenEE_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThirtySevenEE_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtySevenEE_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtySevenEE_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtySevenEE_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtySevenEE_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThirtySevenEE_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtySevenEE_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtySevenEE_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirtySevenEE_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredThirtySevenEE_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredThirtySevenEE_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtySevenEE_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredThirtySevenEE_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThirtySevenEE_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtySevenEE_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredThirtySevenEE_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirtySevenEE_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtySevenEE_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtySevenEE_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtySevenEE_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredThirtySevenEE_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtySevenEE_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredThirtySevenEE_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirtySevenEE_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirtySevenEE_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredThirtySevenEE_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirtySevenEE_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtySevenEE_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredThirtySevenEE_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredThirtySevenEE_619 : Nat.Prime 619 := by norm_num

private theorem prime_oneHundredThirtySevenEE_641 : Nat.Prime 641 := by norm_num

private theorem prime_oneHundredThirtySevenEE_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtySevenEE_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredThirtySevenEE_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredThirtySevenEE_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThirtySevenEE_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThirtySevenEE_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredThirtySevenEE_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredThirtySevenEE_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredThirtySevenEE_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredThirtySevenEE_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredThirtySevenEE_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirtySevenEE_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredThirtySevenEE_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredThirtySevenEE_911 : Nat.Prime 911 := by norm_num

private theorem prime_oneHundredThirtySevenEE_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtySevenEE_953 : Nat.Prime 953 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1237 : Nat.Prime 1237 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1607 : Nat.Prime 1607 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1847 : Nat.Prime 1847 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1913 : Nat.Prime 1913 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1993 : Nat.Prime 1993 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2341 : Nat.Prime 2341 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2591 : Nat.Prime 2591 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2621 : Nat.Prime 2621 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2699 : Nat.Prime 2699 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2711 : Nat.Prime 2711 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2719 : Nat.Prime 2719 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2927 : Nat.Prime 2927 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3917 : Nat.Prime 3917 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4111 : Nat.Prime 4111 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4217 : Nat.Prime 4217 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4259 : Nat.Prime 4259 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4357 : Nat.Prime 4357 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4517 : Nat.Prime 4517 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4583 : Nat.Prime 4583 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5003 : Nat.Prime 5003 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5209 : Nat.Prime 5209 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5281 : Nat.Prime 5281 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5437 : Nat.Prime 5437 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5557 : Nat.Prime 5557 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5827 : Nat.Prime 5827 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5849 : Nat.Prime 5849 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5869 : Nat.Prime 5869 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6217 : Nat.Prime 6217 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6269 : Nat.Prime 6269 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6301 : Nat.Prime 6301 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6571 : Nat.Prime 6571 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6733 : Nat.Prime 6733 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6961 : Nat.Prime 6961 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7127 : Nat.Prime 7127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7129 : Nat.Prime 7129 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7243 : Nat.Prime 7243 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7481 : Nat.Prime 7481 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7649 : Nat.Prime 7649 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7673 : Nat.Prime 7673 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7703 : Nat.Prime 7703 := by norm_num

private theorem prime_oneHundredThirtySevenEE_8539 : Nat.Prime 8539 := by norm_num

private theorem prime_oneHundredThirtySevenEE_8563 : Nat.Prime 8563 := by norm_num

private theorem prime_oneHundredThirtySevenEE_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9227 : Nat.Prime 9227 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9349 : Nat.Prime 9349 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9661 : Nat.Prime 9661 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10169 : Nat.Prime 10169 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10273 : Nat.Prime 10273 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10909 : Nat.Prime 10909 := by norm_num

private theorem prime_oneHundredThirtySevenEE_11197 : Nat.Prime 11197 := by norm_num

private theorem prime_oneHundredThirtySevenEE_11257 : Nat.Prime 11257 := by norm_num

private theorem prime_oneHundredThirtySevenEE_12269 : Nat.Prime 12269 := by norm_num

private theorem prime_oneHundredThirtySevenEE_12637 : Nat.Prime 12637 := by norm_num

private theorem prime_oneHundredThirtySevenEE_13463 : Nat.Prime 13463 := by norm_num

private theorem prime_oneHundredThirtySevenEE_14293 : Nat.Prime 14293 := by norm_num

private theorem prime_oneHundredThirtySevenEE_14639 : Nat.Prime 14639 := by norm_num

private theorem prime_oneHundredThirtySevenEE_14923 : Nat.Prime 14923 := by norm_num

private theorem prime_oneHundredThirtySevenEE_15073 : Nat.Prime 15073 := by norm_num

private theorem prime_oneHundredThirtySevenEE_15173 : Nat.Prime 15173 := by norm_num

private theorem prime_oneHundredThirtySevenEE_15581 : Nat.Prime 15581 := by norm_num

private theorem prime_oneHundredThirtySevenEE_16127 : Nat.Prime 16127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_16369 : Nat.Prime 16369 := by norm_num

private theorem prime_oneHundredThirtySevenEE_16883 : Nat.Prime 16883 := by norm_num

private theorem prime_oneHundredThirtySevenEE_16921 : Nat.Prime 16921 := by norm_num

private theorem prime_oneHundredThirtySevenEE_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtySevenEE_17737 : Nat.Prime 17737 := by norm_num

private theorem prime_oneHundredThirtySevenEE_17959 : Nat.Prime 17959 := by norm_num

private theorem prime_oneHundredThirtySevenEE_18329 : Nat.Prime 18329 := by norm_num

private theorem prime_oneHundredThirtySevenEE_18979 : Nat.Prime 18979 := by norm_num

private theorem prime_oneHundredThirtySevenEE_19249 : Nat.Prime 19249 := by norm_num

private theorem prime_oneHundredThirtySevenEE_19507 : Nat.Prime 19507 := by norm_num

private theorem prime_oneHundredThirtySevenEE_20183 : Nat.Prime 20183 := by norm_num

private theorem prime_oneHundredThirtySevenEE_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtySevenEE_21529 : Nat.Prime 21529 := by norm_num

private theorem prime_oneHundredThirtySevenEE_23549 : Nat.Prime 23549 := by norm_num

private theorem prime_oneHundredThirtySevenEE_23893 : Nat.Prime 23893 := by norm_num

private theorem prime_oneHundredThirtySevenEE_25127 : Nat.Prime 25127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_25717 : Nat.Prime 25717 := by norm_num

private theorem prime_oneHundredThirtySevenEE_27067 : Nat.Prime 27067 := by norm_num

private theorem prime_oneHundredThirtySevenEE_27941 : Nat.Prime 27941 := by norm_num

private theorem prime_oneHundredThirtySevenEE_29311 : Nat.Prime 29311 := by norm_num

private theorem prime_oneHundredThirtySevenEE_30391 : Nat.Prime 30391 := by norm_num

private theorem prime_oneHundredThirtySevenEE_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredThirtySevenEE_32189 : Nat.Prime 32189 := by norm_num

private theorem prime_oneHundredThirtySevenEE_34483 : Nat.Prime 34483 := by norm_num

private theorem prime_oneHundredThirtySevenEE_34781 : Nat.Prime 34781 := by norm_num

private theorem prime_oneHundredThirtySevenEE_34819 : Nat.Prime 34819 := by norm_num

private theorem prime_oneHundredThirtySevenEE_35051 : Nat.Prime 35051 := by norm_num

private theorem prime_oneHundredThirtySevenEE_35671 : Nat.Prime 35671 := by norm_num

private theorem prime_oneHundredThirtySevenEE_36809 : Nat.Prime 36809 := by norm_num

private theorem prime_oneHundredThirtySevenEE_38669 : Nat.Prime 38669 := by norm_num

private theorem prime_oneHundredThirtySevenEE_38711 : Nat.Prime 38711 := by norm_num

private theorem prime_oneHundredThirtySevenEE_39359 : Nat.Prime 39359 := by norm_num

private theorem prime_oneHundredThirtySevenEE_39521 : Nat.Prime 39521 := by norm_num

private theorem prime_oneHundredThirtySevenEE_40699 : Nat.Prime 40699 := by norm_num

private theorem prime_oneHundredThirtySevenEE_43261 : Nat.Prime 43261 := by norm_num

private theorem prime_oneHundredThirtySevenEE_44773 : Nat.Prime 44773 := by norm_num

private theorem prime_oneHundredThirtySevenEE_49559 : Nat.Prime 49559 := by norm_num

private theorem prime_oneHundredThirtySevenEE_51719 : Nat.Prime 51719 := by norm_num

private theorem prime_oneHundredThirtySevenEE_52973 : Nat.Prime 52973 := by norm_num

private theorem prime_oneHundredThirtySevenEE_53993 : Nat.Prime 53993 := by norm_num

private theorem prime_oneHundredThirtySevenEE_54311 : Nat.Prime 54311 := by norm_num

private theorem prime_oneHundredThirtySevenEE_54623 : Nat.Prime 54623 := by norm_num

private theorem prime_oneHundredThirtySevenEE_55127 : Nat.Prime 55127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_57917 : Nat.Prime 57917 := by norm_num

private theorem prime_oneHundredThirtySevenEE_58199 : Nat.Prime 58199 := by norm_num

private theorem prime_oneHundredThirtySevenEE_58913 : Nat.Prime 58913 := by norm_num

private theorem prime_oneHundredThirtySevenEE_59281 : Nat.Prime 59281 := by norm_num

private theorem prime_oneHundredThirtySevenEE_61967 : Nat.Prime 61967 := by norm_num

private theorem prime_oneHundredThirtySevenEE_66271 : Nat.Prime 66271 := by norm_num

private theorem prime_oneHundredThirtySevenEE_69439 : Nat.Prime 69439 := by norm_num

private theorem prime_oneHundredThirtySevenEE_71473 : Nat.Prime 71473 := by norm_num

private theorem prime_oneHundredThirtySevenEE_78803 : Nat.Prime 78803 := by norm_num

private theorem prime_oneHundredThirtySevenEE_82349 : Nat.Prime 82349 := by norm_num

private theorem prime_oneHundredThirtySevenEE_86509 : Nat.Prime 86509 := by norm_num

private theorem prime_oneHundredThirtySevenEE_86531 : Nat.Prime 86531 := by norm_num

private theorem prime_oneHundredThirtySevenEE_91493 : Nat.Prime 91493 := by norm_num

private theorem prime_oneHundredThirtySevenEE_92381 : Nat.Prime 92381 := by norm_num

private theorem prime_oneHundredThirtySevenEE_94099 : Nat.Prime 94099 := by norm_num

private theorem prime_oneHundredThirtySevenEE_96167 : Nat.Prime 96167 := by norm_num

private theorem prime_oneHundredThirtySevenEE_97127 : Nat.Prime 97127 := by norm_num

private theorem prime_oneHundredThirtySevenEE_101281 : Nat.Prime 101281 := by norm_num

private theorem prime_oneHundredThirtySevenEE_103099 : Nat.Prime 103099 := by norm_num

private theorem prime_oneHundredThirtySevenEE_107057 : Nat.Prime 107057 := by norm_num

private theorem prime_oneHundredThirtySevenEE_107923 : Nat.Prime 107923 := by norm_num

private theorem prime_oneHundredThirtySevenEE_108203 : Nat.Prime 108203 := by norm_num

private theorem prime_oneHundredThirtySevenEE_114299 : Nat.Prime 114299 := by norm_num

private theorem prime_oneHundredThirtySevenEE_116663 : Nat.Prime 116663 := by norm_num

private theorem prime_oneHundredThirtySevenEE_118163 : Nat.Prime 118163 := by norm_num

private theorem prime_oneHundredThirtySevenEE_120067 : Nat.Prime 120067 := by norm_num

private theorem prime_oneHundredThirtySevenEE_121171 : Nat.Prime 121171 := by norm_num

private theorem prime_oneHundredThirtySevenEE_122033 : Nat.Prime 122033 := by norm_num

private theorem prime_oneHundredThirtySevenEE_132953 : Nat.Prime 132953 := by norm_num

private theorem prime_oneHundredThirtySevenEE_136531 : Nat.Prime 136531 := by norm_num

private theorem prime_oneHundredThirtySevenEE_136999 : Nat.Prime 136999 := by norm_num

private theorem prime_oneHundredThirtySevenEE_137707 : Nat.Prime 137707 := by norm_num

private theorem prime_oneHundredThirtySevenEE_145307 : Nat.Prime 145307 := by norm_num

private theorem prime_oneHundredThirtySevenEE_146309 : Nat.Prime 146309 := by norm_num

private theorem prime_oneHundredThirtySevenEE_146609 : Nat.Prime 146609 := by norm_num

private theorem prime_oneHundredThirtySevenEE_149323 : Nat.Prime 149323 := by norm_num

private theorem prime_oneHundredThirtySevenEE_154523 : Nat.Prime 154523 := by norm_num

private theorem prime_oneHundredThirtySevenEE_166849 : Nat.Prime 166849 := by norm_num

private theorem prime_oneHundredThirtySevenEE_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtySevenEE_173209 : Nat.Prime 173209 := by norm_num

private theorem prime_oneHundredThirtySevenEE_187931 : Nat.Prime 187931 := by norm_num

private theorem prime_oneHundredThirtySevenEE_191677 : Nat.Prime 191677 := by norm_num

private theorem prime_oneHundredThirtySevenEE_200257 : Nat.Prime 200257 := by norm_num

private theorem prime_oneHundredThirtySevenEE_203249 : Nat.Prime 203249 := by norm_num

private theorem prime_oneHundredThirtySevenEE_203953 : Nat.Prime 203953 := by norm_num

private theorem prime_oneHundredThirtySevenEE_204733 : Nat.Prime 204733 := by norm_num

private theorem prime_oneHundredThirtySevenEE_210401 : Nat.Prime 210401 := by norm_num

private theorem prime_oneHundredThirtySevenEE_214021 : Nat.Prime 214021 := by norm_num

private theorem prime_oneHundredThirtySevenEE_214259 : Nat.Prime 214259 := by norm_num

private theorem prime_oneHundredThirtySevenEE_220757 : Nat.Prime 220757 := by norm_num

private theorem prime_oneHundredThirtySevenEE_225493 : Nat.Prime 225493 := by norm_num

private theorem prime_oneHundredThirtySevenEE_231169 : Nat.Prime 231169 := by norm_num

private theorem prime_oneHundredThirtySevenEE_238099 : Nat.Prime 238099 := by norm_num

private theorem prime_oneHundredThirtySevenEE_256471 : Nat.Prime 256471 := by norm_num

private theorem prime_oneHundredThirtySevenEE_278147 : Nat.Prime 278147 := by norm_num

private theorem prime_oneHundredThirtySevenEE_280769 : Nat.Prime 280769 := by norm_num

private theorem prime_oneHundredThirtySevenEE_288283 : Nat.Prime 288283 := by norm_num

private theorem prime_oneHundredThirtySevenEE_298187 : Nat.Prime 298187 := by norm_num

private theorem prime_oneHundredThirtySevenEE_302513 : Nat.Prime 302513 := by norm_num

private theorem prime_oneHundredThirtySevenEE_311737 : Nat.Prime 311737 := by norm_num

private theorem prime_oneHundredThirtySevenEE_315181 : Nat.Prime 315181 := by norm_num

private theorem prime_oneHundredThirtySevenEE_330439 : Nat.Prime 330439 := by norm_num

private theorem prime_oneHundredThirtySevenEE_337873 : Nat.Prime 337873 := by norm_num

private theorem prime_oneHundredThirtySevenEE_339373 : Nat.Prime 339373 := by norm_num

private theorem prime_oneHundredThirtySevenEE_340079 : Nat.Prime 340079 := by norm_num

private theorem prime_oneHundredThirtySevenEE_349553 : Nat.Prime 349553 := by norm_num

private theorem prime_oneHundredThirtySevenEE_365479 : Nat.Prime 365479 := by norm_num

private theorem prime_oneHundredThirtySevenEE_374293 : Nat.Prime 374293 := by norm_num

private theorem prime_oneHundredThirtySevenEE_388231 : Nat.Prime 388231 := by norm_num

private theorem prime_oneHundredThirtySevenEE_396887 : Nat.Prime 396887 := by norm_num

private theorem prime_oneHundredThirtySevenEE_413879 : Nat.Prime 413879 := by norm_num

private theorem prime_oneHundredThirtySevenEE_419443 : Nat.Prime 419443 := by norm_num

private theorem prime_oneHundredThirtySevenEE_423853 : Nat.Prime 423853 := by norm_num

private theorem prime_oneHundredThirtySevenEE_456581 : Nat.Prime 456581 := by norm_num

private theorem prime_oneHundredThirtySevenEE_492251 : Nat.Prime 492251 := by norm_num

private theorem prime_oneHundredThirtySevenEE_500471 : Nat.Prime 500471 := by norm_num

private theorem prime_oneHundredThirtySevenEE_514889 : Nat.Prime 514889 := by norm_num

private theorem prime_oneHundredThirtySevenEE_520609 : Nat.Prime 520609 := by norm_num

private theorem prime_oneHundredThirtySevenEE_527081 : Nat.Prime 527081 := by norm_num

private theorem prime_oneHundredThirtySevenEE_534601 : Nat.Prime 534601 := by norm_num

private theorem prime_oneHundredThirtySevenEE_538357 : Nat.Prime 538357 := by norm_num

private theorem prime_oneHundredThirtySevenEE_573379 : Nat.Prime 573379 := by norm_num

private theorem prime_oneHundredThirtySevenEE_583783 : Nat.Prime 583783 := by norm_num

private theorem prime_oneHundredThirtySevenEE_588737 : Nat.Prime 588737 := by norm_num

private theorem prime_oneHundredThirtySevenEE_595801 : Nat.Prime 595801 := by norm_num

private theorem prime_oneHundredThirtySevenEE_596917 : Nat.Prime 596917 := by norm_num

private theorem prime_oneHundredThirtySevenEE_650669 : Nat.Prime 650669 := by norm_num

private theorem prime_oneHundredThirtySevenEE_654413 : Nat.Prime 654413 := by norm_num

private theorem prime_oneHundredThirtySevenEE_676829 : Nat.Prime 676829 := by norm_num

private theorem prime_oneHundredThirtySevenEE_697691 : Nat.Prime 697691 := by norm_num

private theorem prime_oneHundredThirtySevenEE_720221 : Nat.Prime 720221 := by norm_num

private theorem prime_oneHundredThirtySevenEE_802441 : Nat.Prime 802441 := by norm_num

private theorem prime_oneHundredThirtySevenEE_804611 : Nat.Prime 804611 := by norm_num

private theorem prime_oneHundredThirtySevenEE_853663 : Nat.Prime 853663 := by norm_num

private theorem prime_oneHundredThirtySevenEE_891907 : Nat.Prime 891907 := by norm_num

private theorem prime_oneHundredThirtySevenEE_940031 : Nat.Prime 940031 := by norm_num

private theorem prime_oneHundredThirtySevenEE_946273 : Nat.Prime 946273 := by norm_num

private theorem prime_oneHundredThirtySevenEE_966631 : Nat.Prime 966631 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1078813 : Nat.Prime 1078813 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1087409 : Nat.Prime 1087409 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1137403 : Nat.Prime 1137403 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1186397 : Nat.Prime 1186397 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1256573 : Nat.Prime 1256573 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1293001 : Nat.Prime 1293001 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1383047 : Nat.Prime 1383047 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1536553 : Nat.Prime 1536553 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1608017 : Nat.Prime 1608017 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1676431 : Nat.Prime 1676431 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1679683 : Nat.Prime 1679683 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1758553 : Nat.Prime 1758553 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1830739 : Nat.Prime 1830739 := by norm_num

private theorem prime_oneHundredThirtySevenEE_1871627 : Nat.Prime 1871627 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2086727 : Nat.Prime 2086727 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2196763 : Nat.Prime 2196763 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2376229 : Nat.Prime 2376229 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2423459 : Nat.Prime 2423459 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2477357 : Nat.Prime 2477357 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2488231 : Nat.Prime 2488231 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2637611 : Nat.Prime 2637611 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2673331 : Nat.Prime 2673331 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2736863 : Nat.Prime 2736863 := by norm_num

private theorem prime_oneHundredThirtySevenEE_2853187 : Nat.Prime 2853187 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3037267 : Nat.Prime 3037267 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3215879 : Nat.Prime 3215879 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3264631 : Nat.Prime 3264631 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3312307 : Nat.Prime 3312307 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3336563 : Nat.Prime 3336563 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3344819 : Nat.Prime 3344819 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3399859 : Nat.Prime 3399859 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3637693 : Nat.Prime 3637693 := by norm_num

private theorem prime_oneHundredThirtySevenEE_3865063 : Nat.Prime 3865063 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4119307 : Nat.Prime 4119307 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4188299 : Nat.Prime 4188299 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4411637 : Nat.Prime 4411637 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4463761 : Nat.Prime 4463761 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4685963 : Nat.Prime 4685963 := by norm_num

private theorem prime_oneHundredThirtySevenEE_4955399 : Nat.Prime 4955399 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5294869 : Nat.Prime 5294869 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5563669 : Nat.Prime 5563669 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5575861 : Nat.Prime 5575861 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5693131 : Nat.Prime 5693131 := by norm_num

private theorem prime_oneHundredThirtySevenEE_5748199 : Nat.Prime 5748199 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6447533 : Nat.Prime 6447533 := by norm_num

private theorem prime_oneHundredThirtySevenEE_6878413 : Nat.Prime 6878413 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7039399 : Nat.Prime 7039399 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7737263 : Nat.Prime 7737263 := by norm_num

private theorem prime_oneHundredThirtySevenEE_7956089 : Nat.Prime 7956089 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9045217 : Nat.Prime 9045217 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9578573 : Nat.Prime 9578573 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9746731 : Nat.Prime 9746731 := by norm_num

private theorem prime_oneHundredThirtySevenEE_9888023 : Nat.Prime 9888023 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10035317 : Nat.Prime 10035317 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10354193 : Nat.Prime 10354193 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10630441 : Nat.Prime 10630441 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10795871 : Nat.Prime 10795871 := by norm_num

private theorem prime_oneHundredThirtySevenEE_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtySevenEE_11021411 : Nat.Prime 11021411 := by norm_num

private theorem prime_oneHundredThirtySevenEE_11293927 : Nat.Prime 11293927 := by norm_num

private theorem prime_oneHundredThirtySevenEE_12422747 : Nat.Prime 12422747 := by norm_num

private theorem prime_oneHundredThirtySevenEE_13294511 : Nat.Prime 13294511 := by norm_num

private theorem prime_oneHundredThirtySevenEE_13505501 : Nat.Prime 13505501 := by norm_num

private theorem prime_oneHundredThirtySevenEE_13835713 : Nat.Prime 13835713 := by norm_num

private theorem prime_oneHundredThirtySevenEE_14020681 : Nat.Prime 14020681 := by norm_num

private theorem prime_oneHundredThirtySevenEE_14620213 : Nat.Prime 14620213 := by norm_num

private theorem prime_oneHundredThirtySevenEE_15650819 : Nat.Prime 15650819 := by norm_num

private theorem prime_oneHundredThirtySevenEE_15804589 : Nat.Prime 15804589 := by norm_num

private theorem prime_oneHundredThirtySevenEE_17522039 : Nat.Prime 17522039 := by norm_num

private theorem prime_oneHundredThirtySevenEE_20452007 : Nat.Prime 20452007 := by norm_num

private theorem prime_oneHundredThirtySevenEE_22002511 : Nat.Prime 22002511 := by norm_num

private theorem prime_oneHundredThirtySevenEE_22547951 : Nat.Prime 22547951 := by norm_num

private theorem prime_oneHundredThirtySevenEE_22896551 : Nat.Prime 22896551 := by norm_num

private theorem prime_oneHundredThirtySevenEE_23415841 : Nat.Prime 23415841 := by norm_num

private theorem prime_oneHundredThirtySevenEE_24976463 : Nat.Prime 24976463 := by norm_num

private theorem prime_oneHundredThirtySevenEE_25678501 : Nat.Prime 25678501 := by norm_num

private theorem prime_oneHundredThirtySevenEE_25826357 : Nat.Prime 25826357 := by norm_num

private theorem prime_oneHundredThirtySevenEE_27723181 : Nat.Prime 27723181 := by norm_num

private theorem prime_oneHundredThirtySevenEE_28433341 : Nat.Prime 28433341 := by norm_num

private theorem prime_oneHundredThirtySevenEE_30575219 : Nat.Prime 30575219 := by
  apply lucas_primality 30575219 (2 : ZMod 30575219)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (804611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (804611, 1)] : List FactorBlock).map factorBlockValue).prod) = 30575219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_804611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30575219) ^ 15287609 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30575219) ^ 1609222 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 30575219) ^ 38 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32007667 : Nat.Prime 32007667 := by
  apply lucas_primality 32007667 (2 : ZMod 32007667)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (280769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (280769, 1)] : List FactorBlock).map factorBlockValue).prod) = 32007667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_280769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32007667) ^ 16003833 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32007667) ^ 10669222 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32007667) ^ 1684614 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32007667) ^ 114 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_33937301 : Nat.Prime 33937301 := by
  apply lucas_primality 33937301 (2 : ZMod 33937301)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (339373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (339373, 1)] : List FactorBlock).map factorBlockValue).prod) = 33937301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_339373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33937301) ^ 16968650 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33937301) ^ 6787460 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33937301) ^ 100 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_34219879 : Nat.Prime 34219879 := by
  apply lucas_primality 34219879 (3 : ZMod 34219879)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (17, 1), (4357, 1)] : List FactorBlock).map factorBlockValue).prod) = 34219879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_4357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34219879) ^ 17109939 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34219879) ^ 11406626 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34219879) ^ 4888554 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34219879) ^ 3110898 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34219879) ^ 2012934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 34219879) ^ 7854 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_38261653 : Nat.Prime 38261653 := by
  apply lucas_primality 38261653 (6 : ZMod 38261653)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (13, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (13, 1), (2027, 1)] : List FactorBlock).map factorBlockValue).prod) = 38261653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_2027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 38261653) ^ 19130826 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38261653) ^ 12753884 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38261653) ^ 3478332 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38261653) ^ 2943204 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 38261653) ^ 18876 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_38650631 : Nat.Prime 38650631 := by
  apply lucas_primality 38650631 (13 : ZMod 38650631)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3865063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3865063, 1)] : List FactorBlock).map factorBlockValue).prod) = 38650631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_3865063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 38650631) ^ 19325315 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 38650631) ^ 7730126 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 38650631) ^ 10 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_45793103 : Nat.Prime 45793103 := by
  apply lucas_primality 45793103 (5 : ZMod 45793103)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22896551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22896551, 1)] : List FactorBlock).map factorBlockValue).prod) = 45793103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_22896551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 45793103) ^ 22896551 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 45793103) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_49952927 : Nat.Prime 49952927 := by
  apply lucas_primality 49952927 (5 : ZMod 49952927)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (24976463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (24976463, 1)] : List FactorBlock).map factorBlockValue).prod) = 49952927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_24976463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 49952927) ^ 24976463 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 49952927) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_51477311 : Nat.Prime 51477311 := by
  apply lucas_primality 51477311 (7 : ZMod 51477311)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (53, 1), (97127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (53, 1), (97127, 1)] : List FactorBlock).map factorBlockValue).prod) = 51477311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_97127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 51477311) ^ 25738655 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51477311) ^ 10295462 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51477311) ^ 971270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 51477311) ^ 530 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_58349651 : Nat.Prime 58349651 := by
  apply lucas_primality 58349651 (2 : ZMod 58349651)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (281, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (281, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) = 58349651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_281
      · exact prime_oneHundredThirtySevenEE_4153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58349651) ^ 29174825 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58349651) ^ 11669930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58349651) ^ 207650 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58349651) ^ 14050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_61915219 : Nat.Prime 61915219 := by
  apply lucas_primality 61915219 (2 : ZMod 61915219)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 2), (19507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 2), (19507, 1)] : List FactorBlock).map factorBlockValue).prod) = 61915219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_19507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61915219) ^ 30957609 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61915219) ^ 20638406 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61915219) ^ 2691966 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 61915219) ^ 3174 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_73245391 : Nat.Prime 73245391 := by
  apply lucas_primality 73245391 (3 : ZMod 73245391)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (419, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (419, 1), (5827, 1)] : List FactorBlock).map factorBlockValue).prod) = 73245391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_419
      · exact prime_oneHundredThirtySevenEE_5827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 73245391) ^ 36622695 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73245391) ^ 24415130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73245391) ^ 14649078 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73245391) ^ 174810 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 73245391) ^ 12570 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_75370901 : Nat.Prime 75370901 := by
  apply lucas_primality 75370901 (2 : ZMod 75370901)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 2), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 2), (6229, 1)] : List FactorBlock).map factorBlockValue).prod) = 75370901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_6229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75370901) ^ 37685450 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75370901) ^ 15074180 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75370901) ^ 6851900 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 75370901) ^ 12100 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_75389383 : Nat.Prime 75389383 := by
  apply lucas_primality 75389383 (6 : ZMod 75389383)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4188299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4188299, 1)] : List FactorBlock).map factorBlockValue).prod) = 75389383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_4188299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 75389383) ^ 37694691 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 75389383) ^ 25129794 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 75389383) ^ 18 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_76411163 : Nat.Prime 76411163 := by
  apply lucas_primality 76411163 (2 : ZMod 76411163)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (179, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (179, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) = 76411163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_61
      · exact prime_oneHundredThirtySevenEE_179
      · exact prime_oneHundredThirtySevenEE_3499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 76411163) ^ 38205581 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76411163) ^ 1252642 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76411163) ^ 426878 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 76411163) ^ 21838 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_83014279 : Nat.Prime 83014279 := by
  apply lucas_primality 83014279 (6 : ZMod 83014279)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13835713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13835713, 1)] : List FactorBlock).map factorBlockValue).prod) = 83014279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13835713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 83014279) ^ 41507139 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 83014279) ^ 27671426 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 83014279) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_87721279 : Nat.Prime 87721279 := by
  apply lucas_primality 87721279 (3 : ZMod 87721279)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14620213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14620213, 1)] : List FactorBlock).map factorBlockValue).prod) = 87721279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_14620213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 87721279) ^ 43860639 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 87721279) ^ 29240426 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 87721279) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_94435499 : Nat.Prime 94435499 := by
  apply lucas_primality 94435499 (2 : ZMod 94435499)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4217, 1), (11197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4217, 1), (11197, 1)] : List FactorBlock).map factorBlockValue).prod) = 94435499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_4217
      · exact prime_oneHundredThirtySevenEE_11197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94435499) ^ 47217749 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94435499) ^ 22394 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 94435499) ^ 8434 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_96671327 : Nat.Prime 96671327 := by
  apply lucas_primality 96671327 (5 : ZMod 96671327)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (613, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (613, 1), (2719, 1)] : List FactorBlock).map factorBlockValue).prod) = 96671327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_613
      · exact prime_oneHundredThirtySevenEE_2719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 96671327) ^ 48335663 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 96671327) ^ 3333494 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 96671327) ^ 157702 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 96671327) ^ 35554 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_100561277 : Nat.Prime 100561277 := by
  apply lucas_primality 100561277 (2 : ZMod 100561277)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (317, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (317, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 100561277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_71
      · exact prime_oneHundredThirtySevenEE_317
      · exact prime_oneHundredThirtySevenEE_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 100561277) ^ 50280638 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100561277) ^ 1416356 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100561277) ^ 317228 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100561277) ^ 90028 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_102954623 : Nat.Prime 102954623 := by
  apply lucas_primality 102954623 (5 : ZMod 102954623)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (51477311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (51477311, 1)] : List FactorBlock).map factorBlockValue).prod) = 102954623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_51477311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 102954623) ^ 51477311 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 102954623) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_109003709 : Nat.Prime 109003709 := by
  apply lucas_primality 109003709 (2 : ZMod 109003709)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (2477357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (2477357, 1)] : List FactorBlock).map factorBlockValue).prod) = 109003709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_2477357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109003709) ^ 54501854 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 109003709) ^ 9909428 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 109003709) ^ 44 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_121986253 : Nat.Prime 121986253 := by
  apply lucas_primality 121986253 (2 : ZMod 121986253)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (443, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (443, 1), (7649, 1)] : List FactorBlock).map factorBlockValue).prod) = 121986253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_443
      · exact prime_oneHundredThirtySevenEE_7649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121986253) ^ 60993126 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121986253) ^ 40662084 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121986253) ^ 275364 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 121986253) ^ 15948 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_132256933 : Nat.Prime 132256933 := by
  apply lucas_primality 132256933 (2 : ZMod 132256933)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11021411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11021411, 1)] : List FactorBlock).map factorBlockValue).prod) = 132256933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11021411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 132256933) ^ 66128466 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 132256933) ^ 44085644 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 132256933) ^ 12 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_133699619 : Nat.Prime 133699619 := by
  apply lucas_primality 133699619 (2 : ZMod 133699619)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (19, 1), (109, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (19, 1), (109, 1), (191, 1)] : List FactorBlock).map factorBlockValue).prod) = 133699619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_109
      · exact prime_oneHundredThirtySevenEE_191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133699619) ^ 66849809 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 133699619) ^ 10284586 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 133699619) ^ 7036822 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 133699619) ^ 1226602 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 133699619) ^ 699998 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_136697243 : Nat.Prime 136697243 := by
  apply lucas_primality 136697243 (5 : ZMod 136697243)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (214259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (214259, 1)] : List FactorBlock).map factorBlockValue).prod) = 136697243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_214259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 136697243) ^ 68348621 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 136697243) ^ 12427022 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 136697243) ^ 4713698 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 136697243) ^ 638 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_148056563 : Nat.Prime 148056563 := by
  apply lucas_primality 148056563 (2 : ZMod 148056563)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (891907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (891907, 1)] : List FactorBlock).map factorBlockValue).prod) = 148056563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_83
      · exact prime_oneHundredThirtySevenEE_891907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 148056563) ^ 74028281 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 148056563) ^ 1783814 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 148056563) ^ 166 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_162369817 : Nat.Prime 162369817 := by
  apply lucas_primality 162369817 (15 : ZMod 162369817)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) = 162369817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_31177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 162369817) ^ 81184908 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 162369817) ^ 54123272 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 162369817) ^ 23195688 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 162369817) ^ 5237736 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 162369817) ^ 5208 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_188870999 : Nat.Prime 188870999 := by
  apply lucas_primality 188870999 (7 : ZMod 188870999)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (94435499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (94435499, 1)] : List FactorBlock).map factorBlockValue).prod) = 188870999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_94435499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 188870999) ^ 94435499 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 188870999) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_194649209 : Nat.Prime 194649209 := by
  apply lucas_primality 194649209 (3 : ZMod 194649209)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (1871627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (1871627, 1)] : List FactorBlock).map factorBlockValue).prod) = 194649209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_1871627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 194649209) ^ 97324604 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 194649209) ^ 14973016 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 194649209) ^ 104 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_198294401 : Nat.Prime 198294401 := by
  apply lucas_primality 198294401 (3 : ZMod 198294401)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 2), (61967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 2), (61967, 1)] : List FactorBlock).map factorBlockValue).prod) = 198294401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_61967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 198294401) ^ 99147200 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 198294401) ^ 39658880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 198294401) ^ 3200 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_203298551 : Nat.Prime 203298551 := by
  apply lucas_primality 203298551 (11 : ZMod 203298551)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 2), (13, 2), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 2), (13, 2), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 203298551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 203298551) ^ 101649275 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 203298551) ^ 40659710 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 203298551) ^ 29042650 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 203298551) ^ 15638350 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 203298551) ^ 414050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_208126759 : Nat.Prime 208126759 := by
  apply lucas_primality 208126759 (6 : ZMod 208126759)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4955399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4955399, 1)] : List FactorBlock).map factorBlockValue).prod) = 208126759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_4955399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 208126759) ^ 104063379 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 208126759) ^ 69375586 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 208126759) ^ 29732394 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 208126759) ^ 42 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_209737753 : Nat.Prime 209737753 := by
  apply lucas_primality 209737753 (15 : ZMod 209737753)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (277, 1), (4507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (277, 1), (4507, 1)] : List FactorBlock).map factorBlockValue).prod) = 209737753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_277
      · exact prime_oneHundredThirtySevenEE_4507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 209737753) ^ 104868876 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 209737753) ^ 69912584 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 209737753) ^ 29962536 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 209737753) ^ 757176 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 209737753) ^ 46536 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_218381377 : Nat.Prime 218381377 := by
  apply lucas_primality 218381377 (5 : ZMod 218381377)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (1137403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (1137403, 1)] : List FactorBlock).map factorBlockValue).prod) = 218381377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_1137403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 218381377) ^ 109190688 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 218381377) ^ 72793792 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 218381377) ^ 192 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_219693203 : Nat.Prime 219693203 := by
  apply lucas_primality 219693203 (2 : ZMod 219693203)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2699, 1), (40699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2699, 1), (40699, 1)] : List FactorBlock).map factorBlockValue).prod) = 219693203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_2699
      · exact prime_oneHundredThirtySevenEE_40699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219693203) ^ 109846601 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 219693203) ^ 81398 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 219693203) ^ 5398 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_267807677 : Nat.Prime 267807677 := by
  apply lucas_primality 267807677 (2 : ZMod 267807677)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (443, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (443, 1), (6571, 1)] : List FactorBlock).map factorBlockValue).prod) = 267807677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_443
      · exact prime_oneHundredThirtySevenEE_6571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 267807677) ^ 133903838 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 267807677) ^ 11643812 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 267807677) ^ 604532 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 267807677) ^ 40756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_270498517 : Nat.Prime 270498517 := by
  apply lucas_primality 270498517 (5 : ZMod 270498517)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (1186397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (1186397, 1)] : List FactorBlock).map factorBlockValue).prod) = 270498517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_1186397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 270498517) ^ 135249258 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 270498517) ^ 90166172 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 270498517) ^ 14236764 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 270498517) ^ 228 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_285922927 : Nat.Prime 285922927 := by
  apply lucas_primality 285922927 (3 : ZMod 285922927)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5294869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5294869, 1)] : List FactorBlock).map factorBlockValue).prod) = 285922927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5294869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 285922927) ^ 142961463 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 285922927) ^ 95307642 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 285922927) ^ 54 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_292243993 : Nat.Prime 292243993 := by
  apply lucas_primality 292243993 (10 : ZMod 292243993)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (179, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (179, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 292243993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_59
      · exact prime_oneHundredThirtySevenEE_179
      · exact prime_oneHundredThirtySevenEE_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 292243993) ^ 146121996 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 292243993) ^ 97414664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 292243993) ^ 4953288 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 292243993) ^ 1632648 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 292243993) ^ 253464 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_306303341 : Nat.Prime 306303341 := by
  apply lucas_primality 306303341 (2 : ZMod 306303341)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (349, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (349, 1), (6269, 1)] : List FactorBlock).map factorBlockValue).prod) = 306303341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_349
      · exact prime_oneHundredThirtySevenEE_6269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 306303341) ^ 153151670 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306303341) ^ 61260668 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306303341) ^ 43757620 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306303341) ^ 877660 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 306303341) ^ 48860 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_308619631 : Nat.Prime 308619631 := by
  apply lucas_primality 308619631 (6 : ZMod 308619631)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (311737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (311737, 1)] : List FactorBlock).map factorBlockValue).prod) = 308619631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_311737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 308619631) ^ 154309815 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 308619631) ^ 102873210 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 308619631) ^ 61723926 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 308619631) ^ 28056330 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 308619631) ^ 990 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_317350489 : Nat.Prime 317350489 := by
  apply lucas_primality 317350489 (34 : ZMod 317350489)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (145307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (145307, 1)] : List FactorBlock).map factorBlockValue).prod) = 317350489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_145307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 317350489) ^ 158675244 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 317350489) ^ 105783496 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 317350489) ^ 45335784 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 317350489) ^ 24411576 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 317350489) ^ 2184 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_343968199 : Nat.Prime 343968199 := by
  apply lucas_primality 343968199 (3 : ZMod 343968199)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (53, 1), (154523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (53, 1), (154523, 1)] : List FactorBlock).map factorBlockValue).prod) = 343968199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_154523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 343968199) ^ 171984099 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 343968199) ^ 114656066 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 343968199) ^ 49138314 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 343968199) ^ 6489966 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 343968199) ^ 2226 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_387047761 : Nat.Prime 387047761 := by
  apply lucas_primality 387047761 (17 : ZMod 387047761)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (11, 1), (146609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (11, 1), (146609, 1)] : List FactorBlock).map factorBlockValue).prod) = 387047761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_146609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 387047761) ^ 193523880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 387047761) ^ 129015920 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 387047761) ^ 77409552 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 387047761) ^ 35186160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 387047761) ^ 2640 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_389869241 : Nat.Prime 389869241 := by
  apply lucas_primality 389869241 (3 : ZMod 389869241)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (9746731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (9746731, 1)] : List FactorBlock).map factorBlockValue).prod) = 389869241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_9746731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 389869241) ^ 194934620 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 389869241) ^ 77973848 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 389869241) ^ 40 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_399014257 : Nat.Prime 399014257 := by
  apply lucas_primality 399014257 (5 : ZMod 399014257)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (353, 1), (23549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (353, 1), (23549, 1)] : List FactorBlock).map factorBlockValue).prod) = 399014257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_353
      · exact prime_oneHundredThirtySevenEE_23549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 399014257) ^ 199507128 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 399014257) ^ 133004752 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 399014257) ^ 1130352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 399014257) ^ 16944 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_447877007 : Nat.Prime 447877007 := by
  apply lucas_primality 447877007 (5 : ZMod 447877007)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (47, 1), (61, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (47, 1), (61, 1), (4111, 1)] : List FactorBlock).map factorBlockValue).prod) = 447877007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_61
      · exact prime_oneHundredThirtySevenEE_4111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 447877007) ^ 223938503 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 447877007) ^ 23572474 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 447877007) ^ 9529298 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 447877007) ^ 7342246 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 447877007) ^ 108946 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_452336299 : Nat.Prime 452336299 := by
  apply lucas_primality 452336299 (3 : ZMod 452336299)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (75389383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (75389383, 1)] : List FactorBlock).map factorBlockValue).prod) = 452336299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_75389383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 452336299) ^ 226168149 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 452336299) ^ 150778766 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 452336299) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_470256971 : Nat.Prime 470256971 := by
  apply lucas_primality 470256971 (2 : ZMod 470256971)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (97, 1), (167, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (97, 1), (167, 1), (2903, 1)] : List FactorBlock).map factorBlockValue).prod) = 470256971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_97
      · exact prime_oneHundredThirtySevenEE_167
      · exact prime_oneHundredThirtySevenEE_2903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 470256971) ^ 235128485 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 470256971) ^ 94051394 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 470256971) ^ 4848010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 470256971) ^ 2815910 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 470256971) ^ 161990 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_472612571 : Nat.Prime 472612571 := by
  apply lucas_primality 472612571 (2 : ZMod 472612571)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (211, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (211, 1), (5209, 1)] : List FactorBlock).map factorBlockValue).prod) = 472612571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_211
      · exact prime_oneHundredThirtySevenEE_5209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472612571) ^ 236306285 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 472612571) ^ 94522514 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 472612571) ^ 10990990 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 472612571) ^ 2239870 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 472612571) ^ 90730 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_478992973 : Nat.Prime 478992973 := by
  apply lucas_primality 478992973 (2 : ZMod 478992973)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (1078813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (1078813, 1)] : List FactorBlock).map factorBlockValue).prod) = 478992973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_1078813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 478992973) ^ 239496486 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 478992973) ^ 159664324 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 478992973) ^ 12945756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 478992973) ^ 444 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_508306637 : Nat.Prime 508306637 := by
  apply lucas_primality 508306637 (2 : ZMod 508306637)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1187, 1), (107057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1187, 1), (107057, 1)] : List FactorBlock).map factorBlockValue).prod) = 508306637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_1187
      · exact prime_oneHundredThirtySevenEE_107057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 508306637) ^ 254153318 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 508306637) ^ 428228 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 508306637) ^ 4748 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_531811613 : Nat.Prime 531811613 := by
  apply lucas_primality 531811613 (3 : ZMod 531811613)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (337, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (337, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 531811613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_337
      · exact prime_oneHundredThirtySevenEE_1009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 531811613) ^ 265905806 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 531811613) ^ 31283036 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 531811613) ^ 23122244 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 531811613) ^ 1578076 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 531811613) ^ 527068 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_531990841 : Nat.Prime 531990841 := by
  apply lucas_primality 531990841 (11 : ZMod 531990841)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (43, 1), (103099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (43, 1), (103099, 1)] : List FactorBlock).map factorBlockValue).prod) = 531990841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_103099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 531990841) ^ 265995420 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 531990841) ^ 177330280 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 531990841) ^ 106398168 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 531990841) ^ 12371880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 531990841) ^ 5160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_580027963 : Nat.Prime 580027963 := by
  apply lucas_primality 580027963 (3 : ZMod 580027963)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (96671327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (96671327, 1)] : List FactorBlock).map factorBlockValue).prod) = 580027963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_96671327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 580027963) ^ 290013981 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 580027963) ^ 193342654 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 580027963) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_586520159 : Nat.Prime 586520159 := by
  apply lucas_primality 586520159 (7 : ZMod 586520159)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (461, 1), (4783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (461, 1), (4783, 1)] : List FactorBlock).map factorBlockValue).prod) = 586520159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_461
      · exact prime_oneHundredThirtySevenEE_4783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 586520159) ^ 293260079 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 586520159) ^ 83788594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 586520159) ^ 30869482 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 586520159) ^ 1272278 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 586520159) ^ 122626 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_610871419 : Nat.Prime 610871419 := by
  apply lucas_primality 610871419 (3 : ZMod 610871419)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (33937301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (33937301, 1)] : List FactorBlock).map factorBlockValue).prod) = 610871419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_33937301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 610871419) ^ 305435709 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 610871419) ^ 203623806 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 610871419) ^ 18 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_667312601 : Nat.Prime 667312601 := by
  apply lucas_primality 667312601 (3 : ZMod 667312601)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (3336563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (3336563, 1)] : List FactorBlock).map factorBlockValue).prod) = 667312601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_3336563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 667312601) ^ 333656300 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 667312601) ^ 133462520 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 667312601) ^ 200 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_688738591 : Nat.Prime 688738591 := by
  apply lucas_primality 688738591 (3 : ZMod 688738591)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (79, 1), (157, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (79, 1), (157, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 688738591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_79
      · exact prime_oneHundredThirtySevenEE_157
      · exact prime_oneHundredThirtySevenEE_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 688738591) ^ 344369295 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688738591) ^ 229579530 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688738591) ^ 137747718 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688738591) ^ 8718210 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688738591) ^ 4386870 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688738591) ^ 1116270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_688959857 : Nat.Prime 688959857 := by
  apply lucas_primality 688959857 (3 : ZMod 688959857)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (3312307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (3312307, 1)] : List FactorBlock).map factorBlockValue).prod) = 688959857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_3312307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 688959857) ^ 344479928 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688959857) ^ 52996912 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 688959857) ^ 208 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_17203
      · exact prime_oneHundredThirtySevenEE_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_789437863 : Nat.Prime 789437863 := by
  apply lucas_primality 789437863 (5 : ZMod 789437863)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (53, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (53, 1), (20183, 1)] : List FactorBlock).map factorBlockValue).prod) = 789437863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_41
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_20183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 789437863) ^ 394718931 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 789437863) ^ 263145954 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 789437863) ^ 19254582 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 789437863) ^ 14895054 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 789437863) ^ 39114 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_800644609 : Nat.Prime 800644609 := by
  apply lucas_primality 800644609 (11 : ZMod 800644609)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 3), (57917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 3), (57917, 1)] : List FactorBlock).map factorBlockValue).prod) = 800644609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_57917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 800644609) ^ 400322304 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 800644609) ^ 266881536 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 800644609) ^ 13824 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_820183459 : Nat.Prime 820183459 := by
  apply lucas_primality 820183459 (2 : ZMod 820183459)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (136697243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (136697243, 1)] : List FactorBlock).map factorBlockValue).prod) = 820183459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_136697243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 820183459) ^ 410091729 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 820183459) ^ 273394486 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 820183459) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_841756367 : Nat.Prime 841756367 := by
  apply lucas_primality 841756367 (5 : ZMod 841756367)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (38261653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (38261653, 1)] : List FactorBlock).map factorBlockValue).prod) = 841756367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_38261653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 841756367) ^ 420878183 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 841756367) ^ 76523306 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 841756367) ^ 22 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_842970277 : Nat.Prime 842970277 := by
  apply lucas_primality 842970277 (2 : ZMod 842970277)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (23415841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (23415841, 1)] : List FactorBlock).map factorBlockValue).prod) = 842970277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_23415841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 842970277) ^ 421485138 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 842970277) ^ 280990092 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 842970277) ^ 36 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_870570979 : Nat.Prime 870570979 := by
  apply lucas_primality 870570979 (2 : ZMod 870570979)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (397, 1), (365479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (397, 1), (365479, 1)] : List FactorBlock).map factorBlockValue).prod) = 870570979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_397
      · exact prime_oneHundredThirtySevenEE_365479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 870570979) ^ 435285489 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 870570979) ^ 290190326 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 870570979) ^ 2192874 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 870570979) ^ 2382 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_872029673 : Nat.Prime 872029673 := by
  apply lucas_primality 872029673 (3 : ZMod 872029673)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (109003709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (109003709, 1)] : List FactorBlock).map factorBlockValue).prod) = 872029673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_109003709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 872029673) ^ 436014836 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 872029673) ^ 8 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_900038849 : Nat.Prime 900038849 := by
  apply lucas_primality 900038849 (3 : ZMod 900038849)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (43, 1), (359, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (43, 1), (359, 1), (911, 1)] : List FactorBlock).map factorBlockValue).prod) = 900038849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_359
      · exact prime_oneHundredThirtySevenEE_911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 900038849) ^ 450019424 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 900038849) ^ 20931136 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 900038849) ^ 2507072 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 900038849) ^ 987968 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_920104981 : Nat.Prime 920104981 := by
  apply lucas_primality 920104981 (7 : ZMod 920104981)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (2203, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (2203, 1), (6961, 1)] : List FactorBlock).map factorBlockValue).prod) = 920104981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_2203
      · exact prime_oneHundredThirtySevenEE_6961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 920104981) ^ 460052490 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 920104981) ^ 306701660 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 920104981) ^ 184020996 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 920104981) ^ 417660 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 920104981) ^ 132180 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1019494547 : Nat.Prime 1019494547 := by
  apply lucas_primality 1019494547 (5 : ZMod 1019494547)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (719, 1), (101281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (719, 1), (101281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1019494547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_719
      · exact prime_oneHundredThirtySevenEE_101281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1019494547) ^ 509747273 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019494547) ^ 145642078 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019494547) ^ 1417934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1019494547) ^ 10066 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1049769179 : Nat.Prime 1049769179 := by
  apply lucas_primality 1049769179 (2 : ZMod 1049769179)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (199, 1), (2637611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (199, 1), (2637611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1049769179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_199
      · exact prime_oneHundredThirtySevenEE_2637611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1049769179) ^ 524884589 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1049769179) ^ 5275222 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1049769179) ^ 398 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1100649967 : Nat.Prime 1100649967 := by
  apply lucas_primality 1100649967 (3 : ZMod 1100649967)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (103, 1), (136999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (103, 1), (136999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100649967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_103
      · exact prime_oneHundredThirtySevenEE_136999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1100649967) ^ 550324983 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100649967) ^ 366883322 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100649967) ^ 84665382 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100649967) ^ 10685922 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1100649967) ^ 8034 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1209325529 : Nat.Prime 1209325529 := by
  apply lucas_primality 1209325529 (3 : ZMod 1209325529)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (7956089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (7956089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1209325529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_7956089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1209325529) ^ 604662764 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1209325529) ^ 63648712 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1209325529) ^ 152 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1235388613 : Nat.Prime 1235388613 := by
  apply lucas_primality 1235388613 (2 : ZMod 1235388613)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (1536553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (1536553, 1)] : List FactorBlock).map factorBlockValue).prod) = 1235388613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_67
      · exact prime_oneHundredThirtySevenEE_1536553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1235388613) ^ 617694306 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235388613) ^ 411796204 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235388613) ^ 18438636 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1235388613) ^ 804 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1540175771 : Nat.Prime 1540175771 := by
  apply lucas_primality 1540175771 (2 : ZMod 1540175771)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (22002511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (22002511, 1)] : List FactorBlock).map factorBlockValue).prod) = 1540175771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_22002511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1540175771) ^ 770087885 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1540175771) ^ 308035154 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1540175771) ^ 220025110 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1540175771) ^ 70 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1727391737 : Nat.Prime 1727391737 := by
  apply lucas_primality 1727391737 (3 : ZMod 1727391737)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (107, 1), (288283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (107, 1), (288283, 1)] : List FactorBlock).map factorBlockValue).prod) = 1727391737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_107
      · exact prime_oneHundredThirtySevenEE_288283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1727391737) ^ 863695868 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1727391737) ^ 246770248 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1727391737) ^ 16143848 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1727391737) ^ 5992 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1856444687 : Nat.Prime 1856444687 := by
  apply lucas_primality 1856444687 (5 : ZMod 1856444687)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (32007667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (32007667, 1)] : List FactorBlock).map factorBlockValue).prod) = 1856444687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_32007667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1856444687) ^ 928222343 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856444687) ^ 64015334 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1856444687) ^ 58 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2084645047 : Nat.Prime 2084645047 := by
  apply lucas_primality 2084645047 (5 : ZMod 2084645047)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (853663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (853663, 1)] : List FactorBlock).map factorBlockValue).prod) = 2084645047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_853663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2084645047) ^ 1042322523 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2084645047) ^ 694881682 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2084645047) ^ 189513186 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2084645047) ^ 56341758 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2084645047) ^ 2442 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2325481373 : Nat.Prime 2325481373 := by
  apply lucas_primality 2325481373 (2 : ZMod 2325481373)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1103, 1), (527081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1103, 1), (527081, 1)] : List FactorBlock).map factorBlockValue).prod) = 2325481373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_1103
      · exact prime_oneHundredThirtySevenEE_527081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2325481373) ^ 1162740686 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2325481373) ^ 2108324 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2325481373) ^ 4412 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2568820993 : Nat.Prime 2568820993 := by
  apply lucas_primality 2568820993 (5 : ZMod 2568820993)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (3344819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (3344819, 1)] : List FactorBlock).map factorBlockValue).prod) = 2568820993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_3344819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2568820993) ^ 1284410496 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2568820993) ^ 856273664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 2568820993) ^ 768 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2685126187 : Nat.Prime 2685126187 := by
  apply lucas_primality 2685126187 (2 : ZMod 2685126187)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (37, 1), (149323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (37, 1), (149323, 1)] : List FactorBlock).map factorBlockValue).prod) = 2685126187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_149323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2685126187) ^ 1342563093 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2685126187) ^ 895042062 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2685126187) ^ 72570978 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2685126187) ^ 17982 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2717989739 : Nat.Prime 2717989739 := by
  apply lucas_primality 2717989739 (2 : ZMod 2717989739)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (127, 1), (239, 1), (44773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (127, 1), (239, 1), (44773, 1)] : List FactorBlock).map factorBlockValue).prod) = 2717989739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_127
      · exact prime_oneHundredThirtySevenEE_239
      · exact prime_oneHundredThirtySevenEE_44773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2717989739) ^ 1358994869 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2717989739) ^ 21401494 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2717989739) ^ 11372342 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2717989739) ^ 60706 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2780503081 : Nat.Prime 2780503081 := by
  apply lucas_primality 2780503081 (7 : ZMod 2780503081)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (47, 1), (439, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (47, 1), (439, 1), (1123, 1)] : List FactorBlock).map factorBlockValue).prod) = 2780503081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_439
      · exact prime_oneHundredThirtySevenEE_1123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2780503081) ^ 1390251540 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2780503081) ^ 926834360 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2780503081) ^ 556100616 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2780503081) ^ 59159640 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2780503081) ^ 6333720 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2780503081) ^ 2475960 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3173504891 : Nat.Prime 3173504891 := by
  apply lucas_primality 3173504891 (2 : ZMod 3173504891)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (317350489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (317350489, 1)] : List FactorBlock).map factorBlockValue).prod) = 3173504891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_317350489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3173504891) ^ 1586752445 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3173504891) ^ 634700978 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3173504891) ^ 10 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3202578437 : Nat.Prime 3202578437 := by
  apply lucas_primality 3202578437 (2 : ZMod 3202578437)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (800644609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (800644609, 1)] : List FactorBlock).map factorBlockValue).prod) = 3202578437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_800644609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3202578437) ^ 1601289218 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3202578437) ^ 4 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3838080737 : Nat.Prime 3838080737 := by
  apply lucas_primality 3838080737 (3 : ZMod 3838080737)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (31, 1), (449, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (31, 1), (449, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) = 3838080737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_449
      · exact prime_oneHundredThirtySevenEE_1231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3838080737) ^ 1919040368 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3838080737) ^ 548297248 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3838080737) ^ 123809056 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3838080737) ^ 8548064 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3838080737) ^ 3117856 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3973033241 : Nat.Prime 3973033241 := by
  apply lucas_primality 3973033241 (3 : ZMod 3973033241)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (79, 1), (114299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (79, 1), (114299, 1)] : List FactorBlock).map factorBlockValue).prod) = 3973033241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_79
      · exact prime_oneHundredThirtySevenEE_114299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3973033241) ^ 1986516620 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973033241) ^ 794606648 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973033241) ^ 361184840 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973033241) ^ 50291560 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3973033241) ^ 34760 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_4132431547 : Nat.Prime 4132431547 := by
  apply lucas_primality 4132431547 (2 : ZMod 4132431547)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (688738591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (688738591, 1)] : List FactorBlock).map factorBlockValue).prod) = 4132431547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_688738591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4132431547) ^ 2066215773 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4132431547) ^ 1377477182 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4132431547) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_4294233539 : Nat.Prime 4294233539 := by
  apply lucas_primality 4294233539 (2 : ZMod 4294233539)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (23, 1), (911, 1), (14639, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (23, 1), (911, 1), (14639, 1)] : List FactorBlock).map factorBlockValue).prod) = 4294233539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_911
      · exact prime_oneHundredThirtySevenEE_14639
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4294233539) ^ 2147116769 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294233539) ^ 613461934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294233539) ^ 186705806 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294233539) ^ 4713758 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4294233539) ^ 293342 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_4508072909 : Nat.Prime 4508072909 := by
  apply lucas_primality 4508072909 (2 : ZMod 4508072909)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7703, 1), (146309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7703, 1), (146309, 1)] : List FactorBlock).map factorBlockValue).prod) = 4508072909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7703
      · exact prime_oneHundredThirtySevenEE_146309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4508072909) ^ 2254036454 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4508072909) ^ 585236 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4508072909) ^ 30812 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5160043373 : Nat.Prime 5160043373 := by
  apply lucas_primality 5160043373 (2 : ZMod 5160043373)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 2), (122033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 2), (122033, 1)] : List FactorBlock).map factorBlockValue).prod) = 5160043373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_122033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5160043373) ^ 2580021686 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160043373) ^ 469094852 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160043373) ^ 166453012 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5160043373) ^ 42284 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5885819189 : Nat.Prime 5885819189 := by
  apply lucas_primality 5885819189 (2 : ZMod 5885819189)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (34219879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (34219879, 1)] : List FactorBlock).map factorBlockValue).prod) = 5885819189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_34219879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5885819189) ^ 2942909594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5885819189) ^ 136879516 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5885819189) ^ 172 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_8238267743 : Nat.Prime 8238267743 := by
  apply lucas_primality 8238267743 (5 : ZMod 8238267743)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (29, 1), (53, 1), (109, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (29, 1), (53, 1), (109, 1), (1069, 1)] : List FactorBlock).map factorBlockValue).prod) = 8238267743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_109
      · exact prime_oneHundredThirtySevenEE_1069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8238267743) ^ 4119133871 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8238267743) ^ 358185554 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8238267743) ^ 284078198 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8238267743) ^ 155439014 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8238267743) ^ 75580438 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8238267743) ^ 7706518 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_8388586891 : Nat.Prime 8388586891 := by
  apply lucas_primality 8388586891 (10 : ZMod 8388586891)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (457, 1), (203953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (457, 1), (203953, 1)] : List FactorBlock).map factorBlockValue).prod) = 8388586891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_457
      · exact prime_oneHundredThirtySevenEE_203953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 8388586891) ^ 4194293445 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8388586891) ^ 2796195630 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8388586891) ^ 1677717378 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8388586891) ^ 18355770 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 8388586891) ^ 41130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_8588467079 : Nat.Prime 8588467079 := by
  apply lucas_primality 8588467079 (11 : ZMod 8588467079)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4294233539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4294233539, 1)] : List FactorBlock).map factorBlockValue).prod) = 8588467079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_4294233539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 8588467079) ^ 4294233539 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 8588467079) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_9016145819 : Nat.Prime 9016145819 := by
  apply lucas_primality 9016145819 (2 : ZMod 9016145819)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4508072909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4508072909, 1)] : List FactorBlock).map factorBlockValue).prod) = 9016145819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_4508072909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 9016145819) ^ 4508072909 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9016145819) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_9489109853 : Nat.Prime 9489109853 := by
  apply lucas_primality 9489109853 (2 : ZMod 9489109853)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (337, 1), (7039399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (337, 1), (7039399, 1)] : List FactorBlock).map factorBlockValue).prod) = 9489109853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_337
      · exact prime_oneHundredThirtySevenEE_7039399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9489109853) ^ 4744554926 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9489109853) ^ 28157596 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9489109853) ^ 1348 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_9562104443 : Nat.Prime 9562104443 := by
  apply lucas_primality 9562104443 (2 : ZMod 9562104443)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (31, 1), (14020681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (31, 1), (14020681, 1)] : List FactorBlock).map factorBlockValue).prod) = 9562104443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_14020681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9562104443) ^ 4781052221 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9562104443) ^ 869282222 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9562104443) ^ 308454982 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 9562104443) ^ 682 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_10903979887 : Nat.Prime 10903979887 := by
  apply lucas_primality 10903979887 (3 : ZMod 10903979887)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (5869, 1), (13463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (5869, 1), (13463, 1)] : List FactorBlock).map factorBlockValue).prod) = 10903979887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_5869
      · exact prime_oneHundredThirtySevenEE_13463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10903979887) ^ 5451989943 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10903979887) ^ 3634659962 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10903979887) ^ 474086082 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10903979887) ^ 1857894 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10903979887) ^ 809922 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_11564981249 : Nat.Prime 11564981249 := by
  apply lucas_primality 11564981249 (3 : ZMod 11564981249)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 10), (11293927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 10), (11293927, 1)] : List FactorBlock).map factorBlockValue).prod) = 11564981249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11293927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11564981249) ^ 5782490624 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11564981249) ^ 1024 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_13320112577 : Nat.Prime 13320112577 := by
  apply lucas_primality 13320112577 (3 : ZMod 13320112577)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (208126759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (208126759, 1)] : List FactorBlock).map factorBlockValue).prod) = 13320112577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_208126759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13320112577) ^ 6660056288 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13320112577) ^ 64 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_13866537697 : Nat.Prime 13866537697 := by
  apply lucas_primality 13866537697 (14 : ZMod 13866537697)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (17, 1), (139, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (17, 1), (139, 1), (5557, 1)] : List FactorBlock).map factorBlockValue).prod) = 13866537697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_139
      · exact prime_oneHundredThirtySevenEE_5557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 13866537697) ^ 6933268848 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (14 : ZMod 13866537697) ^ 4622179232 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (14 : ZMod 13866537697) ^ 1260594336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (14 : ZMod 13866537697) ^ 815678688 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (14 : ZMod 13866537697) ^ 99759264 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (14 : ZMod 13866537697) ^ 2495328 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_14022825907 : Nat.Prime 14022825907 := by
  apply lucas_primality 14022825907 (2 : ZMod 14022825907)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (1979, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (1979, 1), (25127, 1)] : List FactorBlock).map factorBlockValue).prod) = 14022825907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_1979
      · exact prime_oneHundredThirtySevenEE_25127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14022825907) ^ 7011412953 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14022825907) ^ 4674275302 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14022825907) ^ 298357998 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14022825907) ^ 7085814 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 14022825907) ^ 558078 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_14845948849 : Nat.Prime 14845948849 := by
  apply lucas_primality 14845948849 (11 : ZMod 14845948849)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (433, 1), (238099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (433, 1), (238099, 1)] : List FactorBlock).map factorBlockValue).prod) = 14845948849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_433
      · exact prime_oneHundredThirtySevenEE_238099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 14845948849) ^ 7422974424 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 14845948849) ^ 4948649616 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 14845948849) ^ 34286256 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 14845948849) ^ 62352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_15478804751 : Nat.Prime 15478804751 := by
  apply lucas_primality 15478804751 (7 : ZMod 15478804751)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (61915219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (61915219, 1)] : List FactorBlock).map factorBlockValue).prod) = 15478804751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_61915219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 15478804751) ^ 7739402375 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 15478804751) ^ 3095760950 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 15478804751) ^ 250 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_16476535487 : Nat.Prime 16476535487 := by
  apply lucas_primality 16476535487 (5 : ZMod 16476535487)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8238267743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8238267743, 1)] : List FactorBlock).map factorBlockValue).prod) = 16476535487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_8238267743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 16476535487) ^ 8238267743 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 16476535487) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_17485525439 : Nat.Prime 17485525439 := by
  apply lucas_primality 17485525439 (7 : ZMod 17485525439)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (199, 1), (720221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (199, 1), (720221, 1)] : List FactorBlock).map factorBlockValue).prod) = 17485525439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_61
      · exact prime_oneHundredThirtySevenEE_199
      · exact prime_oneHundredThirtySevenEE_720221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 17485525439) ^ 8742762719 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17485525439) ^ 286647958 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17485525439) ^ 87866962 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 17485525439) ^ 24278 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_19084484723 : Nat.Prime 19084484723 := by
  apply lucas_primality 19084484723 (2 : ZMod 19084484723)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (18329, 1), (520609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (18329, 1), (520609, 1)] : List FactorBlock).map factorBlockValue).prod) = 19084484723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_18329
      · exact prime_oneHundredThirtySevenEE_520609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 19084484723) ^ 9542242361 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19084484723) ^ 1041218 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 19084484723) ^ 36658 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_20837992969 : Nat.Prime 20837992969 := by
  apply lucas_primality 20837992969 (11 : ZMod 20837992969)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (19, 1), (887, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (19, 1), (887, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 20837992969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_887
      · exact prime_oneHundredThirtySevenEE_1321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 20837992969) ^ 10418996484 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 20837992969) ^ 6945997656 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 20837992969) ^ 1602922536 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 20837992969) ^ 1096736472 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 20837992969) ^ 23492664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 20837992969) ^ 15774408 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_22685403409 : Nat.Prime 22685403409 := by
  apply lucas_primality 22685403409 (13 : ZMod 22685403409)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (472612571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (472612571, 1)] : List FactorBlock).map factorBlockValue).prod) = 22685403409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_472612571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 22685403409) ^ 11342701704 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 22685403409) ^ 7561801136 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 22685403409) ^ 48 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_23499432763 : Nat.Prime 23499432763 := by
  apply lucas_primality 23499432763 (2 : ZMod 23499432763)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 3), (1129, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 3), (1129, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 23499432763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_1129
      · exact prime_oneHundredThirtySevenEE_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 23499432763) ^ 11749716381 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23499432763) ^ 7833144254 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23499432763) ^ 1807648674 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23499432763) ^ 20814378 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 23499432763) ^ 14882478 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_27467882857 : Nat.Prime 27467882857 := by
  apply lucas_primality 27467882857 (5 : ZMod 27467882857)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (1877, 1), (203249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (1877, 1), (203249, 1)] : List FactorBlock).map factorBlockValue).prod) = 27467882857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_1877
      · exact prime_oneHundredThirtySevenEE_203249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27467882857) ^ 13733941428 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27467882857) ^ 9155960952 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27467882857) ^ 14633928 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 27467882857) ^ 135144 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_27805030811 : Nat.Prime 27805030811 := by
  apply lucas_primality 27805030811 (2 : ZMod 27805030811)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2780503081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2780503081, 1)] : List FactorBlock).map factorBlockValue).prod) = 27805030811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_2780503081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 27805030811) ^ 13902515405 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 27805030811) ^ 5561006162 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 27805030811) ^ 10 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_28060362739 : Nat.Prime 28060362739 := by
  apply lucas_primality 28060362739 (2 : ZMod 28060362739)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2711, 1), (191677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2711, 1), (191677, 1)] : List FactorBlock).map factorBlockValue).prod) = 28060362739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_2711
      · exact prime_oneHundredThirtySevenEE_191677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28060362739) ^ 14030181369 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28060362739) ^ 9353454246 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28060362739) ^ 10350558 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28060362739) ^ 146394 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_28504962349 : Nat.Prime 28504962349 := by
  apply lucas_primality 28504962349 (2 : ZMod 28504962349)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (653, 1), (3637693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (653, 1), (3637693, 1)] : List FactorBlock).map factorBlockValue).prod) = 28504962349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_653
      · exact prime_oneHundredThirtySevenEE_3637693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28504962349) ^ 14252481174 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28504962349) ^ 9501654116 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28504962349) ^ 43652316 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28504962349) ^ 7836 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_29937916097 : Nat.Prime 29937916097 := by
  apply lucas_primality 29937916097 (3 : ZMod 29937916097)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (11, 1), (17, 1), (397, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (11, 1), (17, 1), (397, 1), (6301, 1)] : List FactorBlock).map factorBlockValue).prod) = 29937916097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_397
      · exact prime_oneHundredThirtySevenEE_6301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 29937916097) ^ 14968958048 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29937916097) ^ 2721628736 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29937916097) ^ 1761053888 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29937916097) ^ 75410368 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 29937916097) ^ 4751296 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32701905121 : Nat.Prime 32701905121 := by
  apply lucas_primality 32701905121 (11 : ZMod 32701905121)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (499, 1), (136531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (499, 1), (136531, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701905121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_499
      · exact prime_oneHundredThirtySevenEE_136531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 32701905121) ^ 16350952560 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 32701905121) ^ 10900635040 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 32701905121) ^ 6540381024 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 32701905121) ^ 65534880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 32701905121) ^ 239520 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32950716203 : Nat.Prime 32950716203 := by
  apply lucas_primality 32950716203 (5 : ZMod 32950716203)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (683, 1), (330439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (683, 1), (330439, 1)] : List FactorBlock).map factorBlockValue).prod) = 32950716203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_73
      · exact prime_oneHundredThirtySevenEE_683
      · exact prime_oneHundredThirtySevenEE_330439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32950716203) ^ 16475358101 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 32950716203) ^ 451379674 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 32950716203) ^ 48244094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 32950716203) ^ 99718 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_33154953133 : Nat.Prime 33154953133 := by
  apply lucas_primality 33154953133 (2 : ZMod 33154953133)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (7451, 1), (52973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (7451, 1), (52973, 1)] : List FactorBlock).map factorBlockValue).prod) = 33154953133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_7451
      · exact prime_oneHundredThirtySevenEE_52973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33154953133) ^ 16577476566 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33154953133) ^ 11051651044 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33154953133) ^ 4736421876 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33154953133) ^ 4449732 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33154953133) ^ 625884 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_41635453667 : Nat.Prime 41635453667 := by
  apply lucas_primality 41635453667 (2 : ZMod 41635453667)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (38669, 1), (538357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (38669, 1), (538357, 1)] : List FactorBlock).map factorBlockValue).prod) = 41635453667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_38669
      · exact prime_oneHundredThirtySevenEE_538357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 41635453667) ^ 20817726833 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41635453667) ^ 1076714 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 41635453667) ^ 77338 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_46189843877 : Nat.Prime 46189843877 := by
  apply lucas_primality 46189843877 (2 : ZMod 46189843877)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1049769179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1049769179, 1)] : List FactorBlock).map factorBlockValue).prod) = 46189843877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_1049769179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46189843877) ^ 23094921938 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46189843877) ^ 4199076716 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 46189843877) ^ 44 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_58586589013 : Nat.Prime 58586589013 := by
  apply lucas_primality 58586589013 (2 : ZMod 58586589013)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (2339, 1), (298187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (2339, 1), (298187, 1)] : List FactorBlock).map factorBlockValue).prod) = 58586589013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_2339
      · exact prime_oneHundredThirtySevenEE_298187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58586589013) ^ 29293294506 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58586589013) ^ 19528863004 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58586589013) ^ 8369512716 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58586589013) ^ 25047708 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 58586589013) ^ 196476 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_63894407219 : Nat.Prime 63894407219 := by
  apply lucas_primality 63894407219 (2 : ZMod 63894407219)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1237, 1), (25826357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1237, 1), (25826357, 1)] : List FactorBlock).map factorBlockValue).prod) = 63894407219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_1237
      · exact prime_oneHundredThirtySevenEE_25826357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 63894407219) ^ 31947203609 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63894407219) ^ 51652714 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 63894407219) ^ 2474 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_103403333513 : Nat.Prime 103403333513 := by
  apply lucas_primality 103403333513 (3 : ZMod 103403333513)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (67, 1), (89, 1), (211, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (67, 1), (89, 1), (211, 1), (10273, 1)] : List FactorBlock).map factorBlockValue).prod) = 103403333513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_67
      · exact prime_oneHundredThirtySevenEE_89
      · exact prime_oneHundredThirtySevenEE_211
      · exact prime_oneHundredThirtySevenEE_10273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 103403333513) ^ 51701666756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103403333513) ^ 1543333336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103403333513) ^ 1161835208 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103403333513) ^ 490063192 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 103403333513) ^ 10065544 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_103871430529 : Nat.Prime 103871430529 := by
  apply lucas_primality 103871430529 (7 : ZMod 103871430529)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (270498517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (270498517, 1)] : List FactorBlock).map factorBlockValue).prod) = 103871430529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_270498517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 103871430529) ^ 51935715264 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 103871430529) ^ 34623810176 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 103871430529) ^ 384 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_106623849671 : Nat.Prime 106623849671 := by
  apply lucas_primality 106623849671 (11 : ZMod 106623849671)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (820183459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (820183459, 1)] : List FactorBlock).map factorBlockValue).prod) = 106623849671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_820183459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 106623849671) ^ 53311924835 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 106623849671) ^ 21324769934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 106623849671) ^ 8201834590 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 106623849671) ^ 130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_139460138791 : Nat.Prime 139460138791 := by
  apply lucas_primality 139460138791 (3 : ZMod 139460138791)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (103, 1), (6447533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (103, 1), (6447533, 1)] : List FactorBlock).map factorBlockValue).prod) = 139460138791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_103
      · exact prime_oneHundredThirtySevenEE_6447533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 139460138791) ^ 69730069395 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 139460138791) ^ 46486712930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 139460138791) ^ 27892027758 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 139460138791) ^ 19922876970 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 139460138791) ^ 1353981930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 139460138791) ^ 21630 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_139483091347 : Nat.Prime 139483091347 := by
  apply lucas_primality 139483091347 (2 : ZMod 139483091347)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (43, 1), (311, 1), (91493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (43, 1), (311, 1), (91493, 1)] : List FactorBlock).map factorBlockValue).prod) = 139483091347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_311
      · exact prime_oneHundredThirtySevenEE_91493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139483091347) ^ 69741545673 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 139483091347) ^ 46494363782 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 139483091347) ^ 7341215334 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 139483091347) ^ 3243792822 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 139483091347) ^ 448498686 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 139483091347) ^ 1524522 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_145702305107 : Nat.Prime 145702305107 := by
  apply lucas_primality 145702305107 (2 : ZMod 145702305107)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (37, 1), (877, 1), (118163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (37, 1), (877, 1), (118163, 1)] : List FactorBlock).map factorBlockValue).prod) = 145702305107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_877
      · exact prime_oneHundredThirtySevenEE_118163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145702305107) ^ 72851152553 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 145702305107) ^ 7668542374 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 145702305107) ^ 3937900138 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 145702305107) ^ 166137178 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 145702305107) ^ 1233062 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_164807297143 : Nat.Prime 164807297143 := by
  apply lucas_primality 164807297143 (5 : ZMod 164807297143)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (27467882857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (27467882857, 1)] : List FactorBlock).map factorBlockValue).prod) = 164807297143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_27467882857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 164807297143) ^ 82403648571 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 164807297143) ^ 54935765714 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 164807297143) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_190263842837 : Nat.Prime 190263842837 := by
  apply lucas_primality 190263842837 (2 : ZMod 190263842837)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (92381, 1), (514889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (92381, 1), (514889, 1)] : List FactorBlock).map factorBlockValue).prod) = 190263842837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_92381
      · exact prime_oneHundredThirtySevenEE_514889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 190263842837) ^ 95131921418 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 190263842837) ^ 2059556 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 190263842837) ^ 369524 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_220381151587 : Nat.Prime 220381151587 := by
  apply lucas_primality 220381151587 (2 : ZMod 220381151587)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (32189, 1), (36809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (32189, 1), (36809, 1)] : List FactorBlock).map factorBlockValue).prod) = 220381151587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_32189
      · exact prime_oneHundredThirtySevenEE_36809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 220381151587) ^ 110190575793 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220381151587) ^ 73460383862 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220381151587) ^ 7109069406 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220381151587) ^ 6846474 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 220381151587) ^ 5987154 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_264975222059 : Nat.Prime 264975222059 := by
  apply lucas_primality 264975222059 (2 : ZMod 264975222059)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (49559, 1), (2673331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (49559, 1), (2673331, 1)] : List FactorBlock).map factorBlockValue).prod) = 264975222059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_49559
      · exact prime_oneHundredThirtySevenEE_2673331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 264975222059) ^ 132487611029 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 264975222059) ^ 5346662 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 264975222059) ^ 99118 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_271197206459 : Nat.Prime 271197206459 := by
  apply lucas_primality 271197206459 (2 : ZMod 271197206459)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (251, 1), (28433341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (251, 1), (28433341, 1)] : List FactorBlock).map factorBlockValue).prod) = 271197206459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_251
      · exact prime_oneHundredThirtySevenEE_28433341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 271197206459) ^ 135598603229 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 271197206459) ^ 14273537182 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 271197206459) ^ 1080466958 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 271197206459) ^ 9538 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_373125839467 : Nat.Prime 373125839467 := by
  apply lucas_primality 373125839467 (2 : ZMod 373125839467)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (162369817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (162369817, 1)] : List FactorBlock).map factorBlockValue).prod) = 373125839467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_383
      · exact prime_oneHundredThirtySevenEE_162369817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 373125839467) ^ 186562919733 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373125839467) ^ 124375279822 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373125839467) ^ 974218902 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 373125839467) ^ 2298 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_401807015567 : Nat.Prime 401807015567 := by
  apply lucas_primality 401807015567 (5 : ZMod 401807015567)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 2), (23, 1), (79, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 2), (23, 1), (79, 1), (34781, 1)] : List FactorBlock).map factorBlockValue).prod) = 401807015567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_79
      · exact prime_oneHundredThirtySevenEE_34781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 401807015567) ^ 200903507783 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 401807015567) ^ 36527910506 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 401807015567) ^ 23635706798 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 401807015567) ^ 17469870242 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 401807015567) ^ 5086164754 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 401807015567) ^ 11552486 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_536771808673 : Nat.Prime 536771808673 := by
  apply lucas_primality 536771808673 (15 : ZMod 536771808673)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (508306637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (508306637, 1)] : List FactorBlock).map factorBlockValue).prod) = 536771808673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_508306637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 536771808673) ^ 268385904336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 536771808673) ^ 178923936224 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 536771808673) ^ 48797437152 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (15 : ZMod 536771808673) ^ 1056 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_565261302937 : Nat.Prime 565261302937 := by
  apply lucas_primality 565261302937 (5 : ZMod 565261302937)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (194649209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (194649209, 1)] : List FactorBlock).map factorBlockValue).prod) = 565261302937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_194649209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 565261302937) ^ 282630651468 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 565261302937) ^ 188420434312 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 565261302937) ^ 51387391176 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 565261302937) ^ 2904 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_798980713943 : Nat.Prime 798980713943 := by
  apply lucas_primality 798980713943 (5 : ZMod 798980713943)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23499432763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23499432763, 1)] : List FactorBlock).map factorBlockValue).prod) = 798980713943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_23499432763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 798980713943) ^ 399490356971 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 798980713943) ^ 46998865526 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 798980713943) ^ 34 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1069182899581 : Nat.Prime 1069182899581 := by
  apply lucas_primality 1069182899581 (6 : ZMod 1069182899581)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 1), (383, 1), (2736863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 1), (383, 1), (2736863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1069182899581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_383
      · exact prime_oneHundredThirtySevenEE_2736863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1069182899581) ^ 534591449790 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069182899581) ^ 356394299860 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069182899581) ^ 213836579916 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069182899581) ^ 62893111740 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069182899581) ^ 2791600260 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1069182899581) ^ 390660 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1196250708097 : Nat.Prime 1196250708097 := by
  apply lucas_primality 1196250708097 (5 : ZMod 1196250708097)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (19, 1), (23, 1), (2376229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (19, 1), (23, 1), (2376229, 1)] : List FactorBlock).map factorBlockValue).prod) = 1196250708097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_2376229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1196250708097) ^ 598125354048 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1196250708097) ^ 398750236032 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1196250708097) ^ 62960563584 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1196250708097) ^ 52010900352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1196250708097) ^ 503424 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1391614333231 : Nat.Prime 1391614333231 := by
  apply lucas_primality 1391614333231 (6 : ZMod 1391614333231)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (443, 1), (413879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (23, 1), (443, 1), (413879, 1)] : List FactorBlock).map factorBlockValue).prod) = 1391614333231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_443
      · exact prime_oneHundredThirtySevenEE_413879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1391614333231) ^ 695807166615 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 463871444410 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 278322866646 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 126510393930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 60504971010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 3141341610 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 1391614333231) ^ 3362370 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1409936023319 : Nat.Prime 1409936023319 := by
  apply lucas_primality 1409936023319 (17 : ZMod 1409936023319)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (47, 1), (789437863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (47, 1), (789437863, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409936023319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_789437863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1409936023319) ^ 704968011659 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 1409936023319) ^ 74207159122 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 1409936023319) ^ 29998638794 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 1409936023319) ^ 1786 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1443910781351 : Nat.Prime 1443910781351 := by
  apply lucas_primality 1443910781351 (11 : ZMod 1443910781351)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (101, 1), (285922927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (101, 1), (285922927, 1)] : List FactorBlock).map factorBlockValue).prod) = 1443910781351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_101
      · exact prime_oneHundredThirtySevenEE_285922927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1443910781351) ^ 721955390675 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1443910781351) ^ 288782156270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1443910781351) ^ 14296146350 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 1443910781351) ^ 5050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1698295709237 : Nat.Prime 1698295709237 := by
  apply lucas_primality 1698295709237 (2 : ZMod 1698295709237)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (43, 2), (97, 1), (10909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (43, 2), (97, 1), (10909, 1)] : List FactorBlock).map factorBlockValue).prod) = 1698295709237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_97
      · exact prime_oneHundredThirtySevenEE_10909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1698295709237) ^ 849147854618 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698295709237) ^ 242613672748 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698295709237) ^ 54783732556 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698295709237) ^ 39495249052 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698295709237) ^ 17508203188 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1698295709237) ^ 155678404 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2105869921081 : Nat.Prime 2105869921081 := by
  apply lucas_primality 2105869921081 (42 : ZMod 2105869921081)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (83, 1), (229, 1), (54311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (83, 1), (229, 1), (54311, 1)] : List FactorBlock).map factorBlockValue).prod) = 2105869921081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_83
      · exact prime_oneHundredThirtySevenEE_229
      · exact prime_oneHundredThirtySevenEE_54311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (42 : ZMod 2105869921081) ^ 1052934960540 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 701956640360 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 421173984216 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 123874701240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 25371926760 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 9195938520 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (42 : ZMod 2105869921081) ^ 38774280 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2400683058491 : Nat.Prime 2400683058491 := by
  apply lucas_primality 2400683058491 (2 : ZMod 2400683058491)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (9349, 1), (25678501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (9349, 1), (25678501, 1)] : List FactorBlock).map factorBlockValue).prod) = 2400683058491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_9349
      · exact prime_oneHundredThirtySevenEE_25678501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2400683058491) ^ 1200341529245 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2400683058491) ^ 480136611698 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2400683058491) ^ 256785010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2400683058491) ^ 93490 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2970875699653 : Nat.Prime 2970875699653 := by
  apply lucas_primality 2970875699653 (2 : ZMod 2970875699653)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (53, 1), (667312601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (53, 1), (667312601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2970875699653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_667312601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2970875699653) ^ 1485437849826 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970875699653) ^ 990291899884 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970875699653) ^ 424410814236 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970875699653) ^ 56054258484 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2970875699653) ^ 4452 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3095789630357 : Nat.Prime 3095789630357 := by
  apply lucas_primality 3095789630357 (2 : ZMod 3095789630357)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (59, 1), (452336299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (59, 1), (452336299, 1)] : List FactorBlock).map factorBlockValue).prod) = 3095789630357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_59
      · exact prime_oneHundredThirtySevenEE_452336299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3095789630357) ^ 1547894815178 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095789630357) ^ 106751366564 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095789630357) ^ 52471010684 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3095789630357) ^ 6844 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3889947657703 : Nat.Prime 3889947657703 := by
  apply lucas_primality 3889947657703 (3 : ZMod 3889947657703)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (311, 1), (2084645047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (311, 1), (2084645047, 1)] : List FactorBlock).map factorBlockValue).prod) = 3889947657703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_311
      · exact prime_oneHundredThirtySevenEE_2084645047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3889947657703) ^ 1944973828851 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3889947657703) ^ 1296649219234 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3889947657703) ^ 12507870282 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 3889947657703) ^ 1866 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5146273981201 : Nat.Prime 5146273981201 := by
  apply lucas_primality 5146273981201 (13 : ZMod 5146273981201)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (11, 1), (389869241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (11, 1), (389869241, 1)] : List FactorBlock).map factorBlockValue).prod) = 5146273981201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_389869241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5146273981201) ^ 2573136990600 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 5146273981201) ^ 1715424660400 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 5146273981201) ^ 1029254796240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 5146273981201) ^ 467843089200 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 5146273981201) ^ 13200 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5169475554829 : Nat.Prime 5169475554829 := by
  apply lucas_primality 5169475554829 (26 : ZMod 5169475554829)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (163, 1), (203298551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (163, 1), (203298551, 1)] : List FactorBlock).map factorBlockValue).prod) = 5169475554829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_163
      · exact prime_oneHundredThirtySevenEE_203298551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 5169475554829) ^ 2584737777414 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 5169475554829) ^ 1723158518276 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 5169475554829) ^ 397651965756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 5169475554829) ^ 31714573956 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 5169475554829) ^ 25428 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_6835817220919 : Nat.Prime 6835817220919 := by
  apply lucas_primality 6835817220919 (7 : ZMod 6835817220919)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (739, 1), (4685963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (739, 1), (4685963, 1)] : List FactorBlock).map factorBlockValue).prod) = 6835817220919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_739
      · exact prime_oneHundredThirtySevenEE_4685963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6835817220919) ^ 3417908610459 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6835817220919) ^ 2278605740306 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6835817220919) ^ 976545317274 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6835817220919) ^ 145442919594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6835817220919) ^ 9250090962 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 6835817220919) ^ 1458786 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_6881509109609 : Nat.Prime 6881509109609 := by
  apply lucas_primality 6881509109609 (6 : ZMod 6881509109609)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (227, 1), (5003, 1), (108203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (227, 1), (5003, 1), (108203, 1)] : List FactorBlock).map factorBlockValue).prod) = 6881509109609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_227
      · exact prime_oneHundredThirtySevenEE_5003
      · exact prime_oneHundredThirtySevenEE_108203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 6881509109609) ^ 3440754554804 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6881509109609) ^ 983072729944 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6881509109609) ^ 30315018104 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6881509109609) ^ 1375476536 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 6881509109609) ^ 63598136 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_7244568938059 : Nat.Prime 7244568938059 := by
  apply lucas_primality 7244568938059 (2 : ZMod 7244568938059)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (41635453667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (41635453667, 1)] : List FactorBlock).map factorBlockValue).prod) = 7244568938059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_41635453667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7244568938059) ^ 3622284469029 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244568938059) ^ 2414856312686 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244568938059) ^ 249812722002 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 7244568938059) ^ 174 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_11670997452421 : Nat.Prime 11670997452421 := by
  apply lucas_primality 11670997452421 (6 : ZMod 11670997452421)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (433, 1), (2099, 1), (214021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (433, 1), (2099, 1), (214021, 1)] : List FactorBlock).map factorBlockValue).prod) = 11670997452421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_433
      · exact prime_oneHundredThirtySevenEE_2099
      · exact prime_oneHundredThirtySevenEE_214021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 11670997452421) ^ 5835498726210 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11670997452421) ^ 3890332484140 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11670997452421) ^ 2334199490484 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11670997452421) ^ 26953804740 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11670997452421) ^ 5560265580 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 11670997452421) ^ 54532020 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_12575072082737 : Nat.Prime 12575072082737 := by
  apply lucas_primality 12575072082737 (3 : ZMod 12575072082737)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (231169, 1), (3399859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (231169, 1), (3399859, 1)] : List FactorBlock).map factorBlockValue).prod) = 12575072082737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_231169
      · exact prime_oneHundredThirtySevenEE_3399859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 12575072082737) ^ 6287536041368 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575072082737) ^ 54397744 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12575072082737) ^ 3698704 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_13786932231133 : Nat.Prime 13786932231133 := by
  apply lucas_primality 13786932231133 (6 : ZMod 13786932231133)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (79, 1), (353, 1), (2423459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (79, 1), (353, 1), (2423459, 1)] : List FactorBlock).map factorBlockValue).prod) = 13786932231133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_79
      · exact prime_oneHundredThirtySevenEE_353
      · exact prime_oneHundredThirtySevenEE_2423459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 13786932231133) ^ 6893466115566 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 13786932231133) ^ 4595644077044 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 13786932231133) ^ 810996013596 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 13786932231133) ^ 174518129508 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 13786932231133) ^ 39056465244 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 13786932231133) ^ 5688948 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_14399689673129 : Nat.Prime 14399689673129 := by
  apply lucas_primality 14399689673129 (3 : ZMod 14399689673129)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (47, 1), (1235388613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (47, 1), (1235388613, 1)] : List FactorBlock).map factorBlockValue).prod) = 14399689673129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_1235388613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 14399689673129) ^ 7199844836564 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399689673129) ^ 464506118488 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399689673129) ^ 306376376024 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 14399689673129) ^ 11656 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_16912725761171 : Nat.Prime 16912725761171 := by
  apply lucas_primality 16912725761171 (2 : ZMod 16912725761171)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (89, 1), (379, 1), (761, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (89, 1), (379, 1), (761, 1), (1607, 1)] : List FactorBlock).map factorBlockValue).prod) = 16912725761171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_41
      · exact prime_oneHundredThirtySevenEE_89
      · exact prime_oneHundredThirtySevenEE_379
      · exact prime_oneHundredThirtySevenEE_761
      · exact prime_oneHundredThirtySevenEE_1607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16912725761171) ^ 8456362880585 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 3382545152234 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 412505506370 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 190030626530 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 44624606230 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 22224343970 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 16912725761171) ^ 10524409310 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_22533745421813 : Nat.Prime 22533745421813 := by
  apply lucas_primality 22533745421813 (2 : ZMod 22533745421813)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (619, 1), (478992973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (619, 1), (478992973, 1)] : List FactorBlock).map factorBlockValue).prod) = 22533745421813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_619
      · exact prime_oneHundredThirtySevenEE_478992973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22533745421813) ^ 11266872710906 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533745421813) ^ 1185986601148 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533745421813) ^ 36403465948 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 22533745421813) ^ 47044 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_24025111953187 : Nat.Prime 24025111953187 := by
  apply lucas_primality 24025111953187 (5 : ZMod 24025111953187)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (229, 1), (17485525439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (229, 1), (17485525439, 1)] : List FactorBlock).map factorBlockValue).prod) = 24025111953187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_229
      · exact prime_oneHundredThirtySevenEE_17485525439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24025111953187) ^ 12012555976593 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 24025111953187) ^ 8008370651062 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 24025111953187) ^ 104913152634 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 24025111953187) ^ 1374 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_28799379346259 : Nat.Prime 28799379346259 := by
  apply lucas_primality 28799379346259 (2 : ZMod 28799379346259)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (14399689673129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (14399689673129, 1)] : List FactorBlock).map factorBlockValue).prod) = 28799379346259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_14399689673129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 28799379346259) ^ 14399689673129 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 28799379346259) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_29708756996531 : Nat.Prime 29708756996531 := by
  apply lucas_primality 29708756996531 (2 : ZMod 29708756996531)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2970875699653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2970875699653, 1)] : List FactorBlock).map factorBlockValue).prod) = 29708756996531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_2970875699653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29708756996531) ^ 14854378498265 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29708756996531) ^ 5941751399306 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 29708756996531) ^ 10 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32295834323659 : Nat.Prime 32295834323659 := by
  apply lucas_primality 32295834323659 (10 : ZMod 32295834323659)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (199, 1), (9016145819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (199, 1), (9016145819, 1)] : List FactorBlock).map factorBlockValue).prod) = 32295834323659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_199
      · exact prime_oneHundredThirtySevenEE_9016145819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 32295834323659) ^ 16147917161829 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 32295834323659) ^ 10765278107886 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 32295834323659) ^ 162290624742 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 32295834323659) ^ 3582 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_33838464559657 : Nat.Prime 33838464559657 := by
  apply lucas_primality 33838464559657 (5 : ZMod 33838464559657)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1409936023319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1409936023319, 1)] : List FactorBlock).map factorBlockValue).prod) = 33838464559657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_1409936023319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33838464559657) ^ 16919232279828 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 33838464559657) ^ 11279488186552 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 33838464559657) ^ 24 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_37570580803411 : Nat.Prime 37570580803411 := by
  apply lucas_primality 37570580803411 (3 : ZMod 37570580803411)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71473, 1), (17522039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71473, 1), (17522039, 1)] : List FactorBlock).map factorBlockValue).prod) = 37570580803411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_71473
      · exact prime_oneHundredThirtySevenEE_17522039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37570580803411) ^ 18785290401705 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37570580803411) ^ 12523526934470 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37570580803411) ^ 7514116160682 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37570580803411) ^ 525661170 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 37570580803411) ^ 2144190 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_40199873767661 : Nat.Prime 40199873767661 := by
  apply lucas_primality 40199873767661 (2 : ZMod 40199873767661)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (61, 1), (32950716203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (61, 1), (32950716203, 1)] : List FactorBlock).map factorBlockValue).prod) = 40199873767661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_61
      · exact prime_oneHundredThirtySevenEE_32950716203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40199873767661) ^ 20099936883830 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40199873767661) ^ 8039974753532 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40199873767661) ^ 659014324060 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 40199873767661) ^ 1220 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_46270575343511 : Nat.Prime 46270575343511 := by
  apply lucas_primality 46270575343511 (7 : ZMod 46270575343511)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 3), (23, 1), (586520159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 3), (23, 1), (586520159, 1)] : List FactorBlock).map factorBlockValue).prod) = 46270575343511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_586520159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 46270575343511) ^ 23135287671755 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46270575343511) ^ 9254115068702 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46270575343511) ^ 6610082191930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46270575343511) ^ 2011764145370 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 46270575343511) ^ 78890 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_54719874138143 : Nat.Prime 54719874138143 := by
  apply lucas_primality 54719874138143 (5 : ZMod 54719874138143)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (467, 1), (58586589013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (467, 1), (58586589013, 1)] : List FactorBlock).map factorBlockValue).prod) = 54719874138143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_467
      · exact prime_oneHundredThirtySevenEE_58586589013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 54719874138143) ^ 27359937069071 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 54719874138143) ^ 117173178026 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 54719874138143) ^ 934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_71851680959987 : Nat.Prime 71851680959987 := by
  apply lucas_primality 71851680959987 (2 : ZMod 71851680959987)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14923, 1), (83014279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14923, 1), (83014279, 1)] : List FactorBlock).map factorBlockValue).prod) = 71851680959987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_14923
      · exact prime_oneHundredThirtySevenEE_83014279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 71851680959987) ^ 35925840479993 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 71851680959987) ^ 2477644171034 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 71851680959987) ^ 4814828182 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 71851680959987) ^ 865534 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_86159198864327 : Nat.Prime 86159198864327 := by
  apply lucas_primality 86159198864327 (5 : ZMod 86159198864327)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1549, 1), (3973033241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1549, 1), (3973033241, 1)] : List FactorBlock).map factorBlockValue).prod) = 86159198864327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_1549
      · exact prime_oneHundredThirtySevenEE_3973033241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 86159198864327) ^ 43079599432163 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 86159198864327) ^ 12308456980618 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 86159198864327) ^ 55622465374 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 86159198864327) ^ 21686 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_95918307115471 : Nat.Prime 95918307115471 := by
  apply lucas_primality 95918307115471 (7 : ZMod 95918307115471)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (431, 1), (22547951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (431, 1), (22547951, 1)] : List FactorBlock).map factorBlockValue).prod) = 95918307115471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_431
      · exact prime_oneHundredThirtySevenEE_22547951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 95918307115471) ^ 47959153557735 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 31972769038490 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 19183661423094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 13702615302210 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 2040815045010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 222548276370 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 95918307115471) ^ 4253970 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_115661769896503 : Nat.Prime 115661769896503 := by
  apply lucas_primality 115661769896503 (6 : ZMod 115661769896503)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (239, 1), (349, 1), (2853187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (239, 1), (349, 1), (2853187, 1)] : List FactorBlock).map factorBlockValue).prod) = 115661769896503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_239
      · exact prime_oneHundredThirtySevenEE_349
      · exact prime_oneHundredThirtySevenEE_2853187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 115661769896503) ^ 57830884948251 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 115661769896503) ^ 38553923298834 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 115661769896503) ^ 483940459818 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 115661769896503) ^ 331409082798 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 115661769896503) ^ 40537746 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_162405429905083 : Nat.Prime 162405429905083 := by
  apply lucas_primality 162405429905083 (3 : ZMod 162405429905083)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 2), (173, 1), (132256933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 2), (173, 1), (132256933, 1)] : List FactorBlock).map factorBlockValue).prod) = 162405429905083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_173
      · exact prime_oneHundredThirtySevenEE_132256933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 162405429905083) ^ 81202714952541 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162405429905083) ^ 54135143301694 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162405429905083) ^ 23200775700726 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162405429905083) ^ 12492725377314 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162405429905083) ^ 938759710434 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 162405429905083) ^ 1227954 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_225423484820467 : Nat.Prime 225423484820467 := by
  apply lucas_primality 225423484820467 (2 : ZMod 225423484820467)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37570580803411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37570580803411, 1)] : List FactorBlock).map factorBlockValue).prod) = 225423484820467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_37570580803411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 225423484820467) ^ 112711742410233 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 225423484820467) ^ 75141161606822 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 225423484820467) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_242126208302189 : Nat.Prime 242126208302189 := by
  apply lucas_primality 242126208302189 (2 : ZMod 242126208302189)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (311, 1), (27805030811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (311, 1), (27805030811, 1)] : List FactorBlock).map factorBlockValue).prod) = 242126208302189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_311
      · exact prime_oneHundredThirtySevenEE_27805030811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 242126208302189) ^ 121063104151094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 242126208302189) ^ 34589458328884 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 242126208302189) ^ 778540862708 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 242126208302189) ^ 8708 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_462886294735783 : Nat.Prime 462886294735783 := by
  apply lucas_primality 462886294735783 (6 : ZMod 462886294735783)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (41, 1), (131, 1), (531990841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (41, 1), (131, 1), (531990841, 1)] : List FactorBlock).map factorBlockValue).prod) = 462886294735783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_41
      · exact prime_oneHundredThirtySevenEE_131
      · exact prime_oneHundredThirtySevenEE_531990841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 462886294735783) ^ 231443147367891 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 462886294735783) ^ 154295431578594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 462886294735783) ^ 11289909627702 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 462886294735783) ^ 3533483165922 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 462886294735783) ^ 870102 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_503866700050657 : Nat.Prime 503866700050657 := by
  apply lucas_primality 503866700050657 (5 : ZMod 503866700050657)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (37, 1), (61, 1), (2325481373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (37, 1), (61, 1), (2325481373, 1)] : List FactorBlock).map factorBlockValue).prod) = 503866700050657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_61
      · exact prime_oneHundredThirtySevenEE_2325481373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 503866700050657) ^ 251933350025328 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503866700050657) ^ 167955566683552 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503866700050657) ^ 13618018920288 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503866700050657) ^ 8260109836896 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 503866700050657) ^ 216672 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_537261227282833 : Nat.Prime 537261227282833 := by
  apply lucas_primality 537261227282833 (5 : ZMod 537261227282833)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (41, 1), (139, 1), (1571, 1), (96167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (41, 1), (139, 1), (1571, 1), (96167, 1)] : List FactorBlock).map factorBlockValue).prod) = 537261227282833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_41
      · exact prime_oneHundredThirtySevenEE_139
      · exact prime_oneHundredThirtySevenEE_1571
      · exact prime_oneHundredThirtySevenEE_96167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 537261227282833) ^ 268630613641416 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 179087075760944 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 41327786714064 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 13103932372752 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 3865188685488 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 341986777392 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 537261227282833) ^ 5586752496 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_785128949237221 : Nat.Prime 785128949237221 := by
  apply lucas_primality 785128949237221 (17 : ZMod 785128949237221)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (197, 1), (9489109853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (197, 1), (9489109853, 1)] : List FactorBlock).map factorBlockValue).prod) = 785128949237221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_197
      · exact prime_oneHundredThirtySevenEE_9489109853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 785128949237221) ^ 392564474618610 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 785128949237221) ^ 261709649745740 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 785128949237221) ^ 157025789847444 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 785128949237221) ^ 112161278462460 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 785128949237221) ^ 3985426138260 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 785128949237221) ^ 82740 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_826016733295447 : Nat.Prime 826016733295447 := by
  apply lucas_primality 826016733295447 (5 : ZMod 826016733295447)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (599, 1), (8539, 1), (349553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (599, 1), (8539, 1), (349553, 1)] : List FactorBlock).map factorBlockValue).prod) = 826016733295447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_599
      · exact prime_oneHundredThirtySevenEE_8539
      · exact prime_oneHundredThirtySevenEE_349553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 826016733295447) ^ 413008366647723 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 275338911098482 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 118002390470778 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 75092430299586 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 1378992876954 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 96734598114 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 826016733295447) ^ 2363065782 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_900531579922633 : Nat.Prime 900531579922633 := by
  apply lucas_primality 900531579922633 (10 : ZMod 900531579922633)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (7, 1), (71, 1), (8388586891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (7, 1), (71, 1), (8388586891, 1)] : List FactorBlock).map factorBlockValue).prod) = 900531579922633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_71
      · exact prime_oneHundredThirtySevenEE_8388586891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 900531579922633) ^ 450265789961316 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 900531579922633) ^ 300177193307544 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 900531579922633) ^ 128647368560376 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 900531579922633) ^ 12683543379192 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 900531579922633) ^ 107352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1107182571947891 : Nat.Prime 1107182571947891 := by
  apply lucas_primality 1107182571947891 (2 : ZMod 1107182571947891)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (34483, 1), (188870999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (34483, 1), (188870999, 1)] : List FactorBlock).map factorBlockValue).prod) = 1107182571947891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_34483
      · exact prime_oneHundredThirtySevenEE_188870999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1107182571947891) ^ 553591285973945 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107182571947891) ^ 221436514389578 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107182571947891) ^ 65128386585170 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107182571947891) ^ 32108069830 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107182571947891) ^ 5862110 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1156886637020503 : Nat.Prime 1156886637020503 := by
  apply lucas_primality 1156886637020503 (5 : ZMod 1156886637020503)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (367, 1), (571, 1), (920104981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (367, 1), (571, 1), (920104981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1156886637020503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_367
      · exact prime_oneHundredThirtySevenEE_571
      · exact prime_oneHundredThirtySevenEE_920104981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1156886637020503) ^ 578443318510251 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1156886637020503) ^ 385628879006834 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1156886637020503) ^ 3152279664906 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1156886637020503) ^ 2026071168162 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1156886637020503) ^ 1257342 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1937009666417513 : Nat.Prime 1937009666417513 := by
  apply lucas_primality 1937009666417513 (3 : ZMod 1937009666417513)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (242126208302189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (242126208302189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1937009666417513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_242126208302189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1937009666417513) ^ 968504833208756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1937009666417513) ^ 8 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2251100613903151 : Nat.Prime 2251100613903151 := by
  apply lucas_primality 2251100613903151 (6 : ZMod 2251100613903151)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (103, 1), (145702305107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (103, 1), (145702305107, 1)] : List FactorBlock).map factorBlockValue).prod) = 2251100613903151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_103
      · exact prime_oneHundredThirtySevenEE_145702305107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2251100613903151) ^ 1125550306951575 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2251100613903151) ^ 750366871301050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2251100613903151) ^ 450220122780630 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2251100613903151) ^ 21855345766050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 2251100613903151) ^ 15450 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2526138413817659 : Nat.Prime 2526138413817659 := by
  apply lucas_primality 2526138413817659 (2 : ZMod 2526138413817659)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10354193, 1), (121986253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10354193, 1), (121986253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2526138413817659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_10354193
      · exact prime_oneHundredThirtySevenEE_121986253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2526138413817659) ^ 1263069206908829 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2526138413817659) ^ 243972506 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2526138413817659) ^ 20708386 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2601986632578941 : Nat.Prime 2601986632578941 := by
  apply lucas_primality 2601986632578941 (3 : ZMod 2601986632578941)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (719, 1), (225493, 1), (802441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (719, 1), (225493, 1), (802441, 1)] : List FactorBlock).map factorBlockValue).prod) = 2601986632578941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_719
      · exact prime_oneHundredThirtySevenEE_225493
      · exact prime_oneHundredThirtySevenEE_802441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2601986632578941) ^ 1300993316289470 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2601986632578941) ^ 520397326515788 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2601986632578941) ^ 3618896568260 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2601986632578941) ^ 11539101580 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2601986632578941) ^ 3242589340 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3094989824463283 : Nat.Prime 3094989824463283 := by
  apply lucas_primality 3094989824463283 (2 : ZMod 3094989824463283)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (47, 1), (809, 1), (7243, 1), (21529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (47, 1), (809, 1), (7243, 1), (21529, 1)] : List FactorBlock).map factorBlockValue).prod) = 3094989824463283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_47
      · exact prime_oneHundredThirtySevenEE_809
      · exact prime_oneHundredThirtySevenEE_7243
      · exact prime_oneHundredThirtySevenEE_21529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3094989824463283) ^ 1547494912231641 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 1031663274821094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 106723787050458 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 65850847329006 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 3825698176098 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 427307721174 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3094989824463283) ^ 143759107458 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3448058945866189 : Nat.Prime 3448058945866189 := by
  apply lucas_primality 3448058945866189 (6 : ZMod 3448058945866189)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (199, 1), (1443910781351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (199, 1), (1443910781351, 1)] : List FactorBlock).map factorBlockValue).prod) = 3448058945866189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_199
      · exact prime_oneHundredThirtySevenEE_1443910781351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 3448058945866189) ^ 1724029472933094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3448058945866189) ^ 1149352981955396 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3448058945866189) ^ 17326929376212 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 3448058945866189) ^ 2388 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3516804934767679 : Nat.Prime 3516804934767679 := by
  apply lucas_primality 3516804934767679 (11 : ZMod 3516804934767679)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5693131, 1), (102954623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5693131, 1), (102954623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3516804934767679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5693131
      · exact prime_oneHundredThirtySevenEE_102954623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3516804934767679) ^ 1758402467383839 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3516804934767679) ^ 1172268311589226 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3516804934767679) ^ 617727738 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 3516804934767679) ^ 34158786 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3826389417466669 : Nat.Prime 3826389417466669 := by
  apply lucas_primality 3826389417466669 (2 : ZMod 3826389417466669)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (166849, 1), (7737263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (166849, 1), (7737263, 1)] : List FactorBlock).map factorBlockValue).prod) = 3826389417466669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_166849
      · exact prime_oneHundredThirtySevenEE_7737263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3826389417466669) ^ 1913194708733334 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3826389417466669) ^ 1275463139155556 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3826389417466669) ^ 294337647497436 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3826389417466669) ^ 201388916708772 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3826389417466669) ^ 22933247532 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3826389417466669) ^ 494540436 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_4012512328910387 : Nat.Prime 4012512328910387 := by
  apply lucas_primality 4012512328910387 (2 : ZMod 4012512328910387)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (53, 1), (59, 1), (66271, 1), (1383047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (53, 1), (59, 1), (66271, 1), (1383047, 1)] : List FactorBlock).map factorBlockValue).prod) = 4012512328910387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_59
      · exact prime_oneHundredThirtySevenEE_66271
      · exact prime_oneHundredThirtySevenEE_1383047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4012512328910387) ^ 2006256164455193 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012512328910387) ^ 573216046987198 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012512328910387) ^ 75707779790762 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012512328910387) ^ 68008683540854 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012512328910387) ^ 60547031566 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 4012512328910387) ^ 2901211838 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5052276827635319 : Nat.Prime 5052276827635319 := by
  apply lucas_primality 5052276827635319 (7 : ZMod 5052276827635319)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2526138413817659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2526138413817659, 1)] : List FactorBlock).map factorBlockValue).prod) = 5052276827635319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_2526138413817659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 5052276827635319) ^ 2526138413817659 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 5052276827635319) ^ 2 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_6643095431687347 : Nat.Prime 6643095431687347 := by
  apply lucas_primality 6643095431687347 (5 : ZMod 6643095431687347)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1107182571947891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1107182571947891, 1)] : List FactorBlock).map factorBlockValue).prod) = 6643095431687347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_1107182571947891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6643095431687347) ^ 3321547715843673 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6643095431687347) ^ 2214365143895782 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 6643095431687347) ^ 6 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_9926591206415761 : Nat.Prime 9926591206415761 := by
  apply lucas_primality 9926591206415761 (7 : ZMod 9926591206415761)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (13786932231133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (13786932231133, 1)] : List FactorBlock).map factorBlockValue).prod) = 9926591206415761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13786932231133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9926591206415761) ^ 4963295603207880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 9926591206415761) ^ 3308863735471920 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 9926591206415761) ^ 1985318241283152 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 9926591206415761) ^ 720 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_12375690342882161 : Nat.Prime 12375690342882161 := by
  apply lucas_primality 12375690342882161 (3 : ZMod 12375690342882161)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (1109, 1), (4517, 1), (4411637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (1109, 1), (4517, 1), (4411637, 1)] : List FactorBlock).map factorBlockValue).prod) = 12375690342882161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_1109
      · exact prime_oneHundredThirtySevenEE_4517
      · exact prime_oneHundredThirtySevenEE_4411637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12375690342882161) ^ 6187845171441080 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12375690342882161) ^ 2475138068576432 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12375690342882161) ^ 1767955763268880 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12375690342882161) ^ 11159324024240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12375690342882161) ^ 2739803042480 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 12375690342882161) ^ 2805237680 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_23551150039774009 : Nat.Prime 23551150039774009 := by
  apply lucas_primality 23551150039774009 (19 : ZMod 23551150039774009)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2086727, 1), (470256971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2086727, 1), (470256971, 1)] : List FactorBlock).map factorBlockValue).prod) = 23551150039774009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_2086727
      · exact prime_oneHundredThirtySevenEE_470256971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 23551150039774009) ^ 11775575019887004 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 23551150039774009) ^ 7850383346591336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 23551150039774009) ^ 11286167304 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 23551150039774009) ^ 50081448 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_23553868477116631 : Nat.Prime 23553868477116631 := by
  apply lucas_primality 23553868477116631 (6 : ZMod 23553868477116631)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (785128949237221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (785128949237221, 1)] : List FactorBlock).map factorBlockValue).prod) = 23553868477116631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_785128949237221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 23553868477116631) ^ 11776934238558315 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 23553868477116631) ^ 7851289492372210 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 23553868477116631) ^ 4710773695423326 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 23553868477116631) ^ 30 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_26383852187426761 : Nat.Prime 26383852187426761 := by
  apply lucas_primality 26383852187426761 (7 : ZMod 26383852187426761)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (16912725761171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (16912725761171, 1)] : List FactorBlock).map factorBlockValue).prod) = 26383852187426761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_16912725761171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26383852187426761) ^ 13191926093713380 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26383852187426761) ^ 8794617395808920 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26383852187426761) ^ 5276770437485352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26383852187426761) ^ 2029527091340520 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 26383852187426761) ^ 1560 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32526952606910261 : Nat.Prime 32526952606910261 := by
  apply lucas_primality 32526952606910261 (2 : ZMod 32526952606910261)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (315181, 1), (5160043373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (315181, 1), (5160043373, 1)] : List FactorBlock).map factorBlockValue).prod) = 32526952606910261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_315181
      · exact prime_oneHundredThirtySevenEE_5160043373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32526952606910261) ^ 16263476303455130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32526952606910261) ^ 6505390521382052 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32526952606910261) ^ 103200867460 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32526952606910261) ^ 6303620 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_35318414345352367 : Nat.Prime 35318414345352367 := by
  apply lucas_primality 35318414345352367 (5 : ZMod 35318414345352367)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (8807, 1), (204733, 1), (3264631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (8807, 1), (204733, 1), (3264631, 1)] : List FactorBlock).map factorBlockValue).prod) = 35318414345352367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_8807
      · exact prime_oneHundredThirtySevenEE_204733
      · exact prime_oneHundredThirtySevenEE_3264631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 35318414345352367) ^ 17659207172676183 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35318414345352367) ^ 11772804781784122 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35318414345352367) ^ 4010266191138 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35318414345352367) ^ 172509631302 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 35318414345352367) ^ 10818501186 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_38850455929128191 : Nat.Prime 38850455929128191 := by
  apply lucas_primality 38850455929128191 (17 : ZMod 38850455929128191)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (116663, 1), (900038849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (116663, 1), (900038849, 1)] : List FactorBlock).map factorBlockValue).prod) = 38850455929128191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_37
      · exact prime_oneHundredThirtySevenEE_116663
      · exact prime_oneHundredThirtySevenEE_900038849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 38850455929128191) ^ 19425227964564095 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 38850455929128191) ^ 7770091185825638 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 38850455929128191) ^ 1050012322408870 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 38850455929128191) ^ 333014374130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 38850455929128191) ^ 43165310 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_57168278901213269 : Nat.Prime 57168278901213269 := by
  apply lucas_primality 57168278901213269 (2 : ZMod 57168278901213269)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5563669, 1), (2568820993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5563669, 1), (2568820993, 1)] : List FactorBlock).map factorBlockValue).prod) = 57168278901213269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5563669
      · exact prime_oneHundredThirtySevenEE_2568820993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 57168278901213269) ^ 28584139450606634 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 57168278901213269) ^ 10275283972 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 57168278901213269) ^ 22254676 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_73399437307837453 : Nat.Prime 73399437307837453 := by
  apply lucas_primality 73399437307837453 (2 : ZMod 73399437307837453)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (17, 1), (197, 1), (409, 1), (5849, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (17, 1), (197, 1), (409, 1), (5849, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) = 73399437307837453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_197
      · exact prime_oneHundredThirtySevenEE_409
      · exact prime_oneHundredThirtySevenEE_5849
      · exact prime_oneHundredThirtySevenEE_15581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 73399437307837453) ^ 36699718653918726 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 24466479102612484 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 10485633901119636 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 4317613959284556 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 372585976181916 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 179460726914028 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 12549057498348 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 73399437307837453) ^ 4710829684092 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_91106652830484233 : Nat.Prime 91106652830484233 := by
  apply lucas_primality 91106652830484233 (3 : ZMod 91106652830484233)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (331, 1), (39521, 1), (870570979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (331, 1), (39521, 1), (870570979, 1)] : List FactorBlock).map factorBlockValue).prod) = 91106652830484233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_331
      · exact prime_oneHundredThirtySevenEE_39521
      · exact prime_oneHundredThirtySevenEE_870570979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 91106652830484233) ^ 45553326415242116 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91106652830484233) ^ 275246685288472 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91106652830484233) ^ 2305271952392 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 91106652830484233) ^ 104651608 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_94994762261972689 : Nat.Prime 94994762261972689 := by
  apply lucas_primality 94994762261972689 (19 : ZMod 94994762261972689)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (617, 1), (1069182899581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (617, 1), (1069182899581, 1)] : List FactorBlock).map factorBlockValue).prod) = 94994762261972689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_617
      · exact prime_oneHundredThirtySevenEE_1069182899581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 94994762261972689) ^ 47497381130986344 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 94994762261972689) ^ 31664920753990896 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 94994762261972689) ^ 153962337539664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (19 : ZMod 94994762261972689) ^ 88848 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_109553659611460397 : Nat.Prime 109553659611460397 := by
  apply lucas_primality 109553659611460397 (2 : ZMod 109553659611460397)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16127, 1), (1698295709237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16127, 1), (1698295709237, 1)] : List FactorBlock).map factorBlockValue).prod) = 109553659611460397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_16127
      · exact prime_oneHundredThirtySevenEE_1698295709237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 109553659611460397) ^ 54776829805730198 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 109553659611460397) ^ 6793182836948 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 109553659611460397) ^ 64508 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_111574980085723351 : Nat.Prime 111574980085723351 := by
  apply lucas_primality 111574980085723351 (26 : ZMod 111574980085723351)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (251, 1), (1061, 1), (399014257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (251, 1), (1061, 1), (399014257, 1)] : List FactorBlock).map factorBlockValue).prod) = 111574980085723351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_251
      · exact prime_oneHundredThirtySevenEE_1061
      · exact prime_oneHundredThirtySevenEE_399014257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 111574980085723351) ^ 55787490042861675 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 37191660028574450 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 22314996017144670 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 15939282869389050 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 444521833010850 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 105160207432350 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (26 : ZMod 111574980085723351) ^ 279626550 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_113507838188633659 : Nat.Prime 113507838188633659 := by
  apply lucas_primality 113507838188633659 (2 : ZMod 113507838188633659)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (397, 1), (7127, 1), (337873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (257, 1), (397, 1), (7127, 1), (337873, 1)] : List FactorBlock).map factorBlockValue).prod) = 113507838188633659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_257
      · exact prime_oneHundredThirtySevenEE_397
      · exact prime_oneHundredThirtySevenEE_7127
      · exact prime_oneHundredThirtySevenEE_337873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 113507838188633659) ^ 56753919094316829 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 37835946062877886 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 16215405455519094 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 10318894380784878 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 441664740033594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 285913950097314 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 15926454074454 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 113507838188633659) ^ 335948235546 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_119892553151709467 : Nat.Prime 119892553151709467 := by
  apply lucas_primality 119892553151709467 (2 : ZMod 119892553151709467)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (54623, 1), (69439, 1), (15804589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (54623, 1), (69439, 1), (15804589, 1)] : List FactorBlock).map factorBlockValue).prod) = 119892553151709467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_54623
      · exact prime_oneHundredThirtySevenEE_69439
      · exact prime_oneHundredThirtySevenEE_15804589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 119892553151709467) ^ 59946276575854733 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119892553151709467) ^ 2194909711142 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119892553151709467) ^ 1726588129894 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 119892553151709467) ^ 7585932994 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_155997994672005949 : Nat.Prime 155997994672005949 := by
  apply lucas_primality 155997994672005949 (2 : ZMod 155997994672005949)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 2), (11, 1), (29, 1), (163, 1), (929, 1), (1830739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 2), (11, 1), (29, 1), (163, 1), (929, 1), (1830739, 1)] : List FactorBlock).map factorBlockValue).prod) = 155997994672005949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_163
      · exact prime_oneHundredThirtySevenEE_929
      · exact prime_oneHundredThirtySevenEE_1830739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 155997994672005949) ^ 77998997336002974 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 51999331557335316 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 22285427810286564 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 14181635879273268 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 5379241195586412 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 957042912098196 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 167920338721212 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 155997994672005949) ^ 85210395732 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_161138972186560037 : Nat.Prime 161138972186560037 := by
  apply lucas_primality 161138972186560037 (2 : ZMod 161138972186560037)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (397, 1), (953, 1), (82349, 1), (1293001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (397, 1), (953, 1), (82349, 1), (1293001, 1)] : List FactorBlock).map factorBlockValue).prod) = 161138972186560037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_397
      · exact prime_oneHundredThirtySevenEE_953
      · exact prime_oneHundredThirtySevenEE_82349
      · exact prime_oneHundredThirtySevenEE_1293001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 161138972186560037) ^ 80569486093280018 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 161138972186560037) ^ 405891617598388 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 161138972186560037) ^ 169086014886212 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 161138972186560037) ^ 1956781165364 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 161138972186560037) ^ 124624012036 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_259082811173200291 : Nat.Prime 259082811173200291 := by
  apply lucas_primality 259082811173200291 (3 : ZMod 259082811173200291)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (587, 1), (940031, 1), (15650819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (587, 1), (940031, 1), (15650819, 1)] : List FactorBlock).map factorBlockValue).prod) = 259082811173200291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_587
      · exact prime_oneHundredThirtySevenEE_940031
      · exact prime_oneHundredThirtySevenEE_15650819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 259082811173200291) ^ 129541405586600145 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 259082811173200291) ^ 86360937057733430 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 259082811173200291) ^ 51816562234640058 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 259082811173200291) ^ 441367651061670 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 259082811173200291) ^ 275610922590 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 259082811173200291) ^ 16553945910 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_296241555478489393 : Nat.Prime 296241555478489393 := by
  apply lucas_primality 296241555478489393 (5 : ZMod 296241555478489393)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1608017, 1), (3838080737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1608017, 1), (3838080737, 1)] : List FactorBlock).map factorBlockValue).prod) = 296241555478489393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_1608017
      · exact prime_oneHundredThirtySevenEE_3838080737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 296241555478489393) ^ 148120777739244696 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 296241555478489393) ^ 98747185159496464 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 296241555478489393) ^ 184227875376 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 296241555478489393) ^ 77184816 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_298621370841026021 : Nat.Prime 298621370841026021 := by
  apply lucas_primality 298621370841026021 (3 : ZMod 298621370841026021)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (456581, 1), (32701905121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (456581, 1), (32701905121, 1)] : List FactorBlock).map factorBlockValue).prod) = 298621370841026021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_456581
      · exact prime_oneHundredThirtySevenEE_32701905121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 298621370841026021) ^ 149310685420513010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 298621370841026021) ^ 59724274168205204 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 298621370841026021) ^ 654038102420 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 298621370841026021) ^ 9131620 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_454031352754534637 : Nat.Prime 454031352754534637 := by
  apply lucas_primality 454031352754534637 (2 : ZMod 454031352754534637)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113507838188633659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113507838188633659, 1)] : List FactorBlock).map factorBlockValue).prod) = 454031352754534637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_113507838188633659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 454031352754534637) ^ 227015676377267318 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 454031352754534637) ^ 4 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_486813956170052369 : Nat.Prime 486813956170052369 := by
  apply lucas_primality 486813956170052369 (3 : ZMod 486813956170052369)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (13, 1), (15173, 1), (14022825907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (13, 1), (15173, 1), (14022825907, 1)] : List FactorBlock).map factorBlockValue).prod) = 486813956170052369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_15173
      · exact prime_oneHundredThirtySevenEE_14022825907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 486813956170052369) ^ 243406978085026184 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486813956170052369) ^ 44255814197277488 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486813956170052369) ^ 37447227397696336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486813956170052369) ^ 32084225675216 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 486813956170052369) ^ 34715824 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_511370551934223433 : Nat.Prime 511370551934223433 := by
  apply lucas_primality 511370551934223433 (10 : ZMod 511370551934223433)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (1937009666417513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (1937009666417513, 1)] : List FactorBlock).map factorBlockValue).prod) = 511370551934223433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_1937009666417513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 511370551934223433) ^ 255685275967111716 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 511370551934223433) ^ 170456850644741144 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 511370551934223433) ^ 46488231994020312 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 511370551934223433) ^ 264 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_598234346866585679 : Nat.Prime 598234346866585679 := by
  apply lucas_primality 598234346866585679 (17 : ZMod 598234346866585679)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (223, 1), (534601, 1), (58349651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (223, 1), (534601, 1), (58349651, 1)] : List FactorBlock).map factorBlockValue).prod) = 598234346866585679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_223
      · exact prime_oneHundredThirtySevenEE_534601
      · exact prime_oneHundredThirtySevenEE_58349651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 598234346866585679) ^ 299117173433292839 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 598234346866585679) ^ 13912426671315946 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 598234346866585679) ^ 2682665232585586 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 598234346866585679) ^ 1119029606878 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 598234346866585679) ^ 10252577978 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_607797165753850771 : Nat.Prime 607797165753850771 := by
  apply lucas_primality 607797165753850771 (2 : ZMod 607797165753850771)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (2251100613903151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (2251100613903151, 1)] : List FactorBlock).map factorBlockValue).prod) = 607797165753850771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_2251100613903151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 607797165753850771) ^ 303898582876925385 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 607797165753850771) ^ 202599055251283590 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 607797165753850771) ^ 121559433150770154 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 607797165753850771) ^ 270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_622349920854818743 : Nat.Prime 622349920854818743 := by
  apply lucas_primality 622349920854818743 (3 : ZMod 622349920854818743)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15073, 1), (6881509109609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15073, 1), (6881509109609, 1)] : List FactorBlock).map factorBlockValue).prod) = 622349920854818743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_15073
      · exact prime_oneHundredThirtySevenEE_6881509109609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 622349920854818743) ^ 311174960427409371 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 622349920854818743) ^ 207449973618272914 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 622349920854818743) ^ 41289054657654 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 622349920854818743) ^ 90438 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_640415382921136937 : Nat.Prime 640415382921136937 := by
  apply lucas_primality 640415382921136937 (3 : ZMod 640415382921136937)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (149, 1), (537261227282833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (149, 1), (537261227282833, 1)] : List FactorBlock).map factorBlockValue).prod) = 640415382921136937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_149
      · exact prime_oneHundredThirtySevenEE_537261227282833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 640415382921136937) ^ 320207691460568468 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 640415382921136937) ^ 4298089818262664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 640415382921136937) ^ 1192 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_824642340938607479 : Nat.Prime 824642340938607479 := by
  apply lucas_primality 824642340938607479 (7 : ZMod 824642340938607479)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1993, 1), (966631, 1), (30575219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1993, 1), (966631, 1), (30575219, 1)] : List FactorBlock).map factorBlockValue).prod) = 824642340938607479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_1993
      · exact prime_oneHundredThirtySevenEE_966631
      · exact prime_oneHundredThirtySevenEE_30575219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 824642340938607479) ^ 412321170469303739 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 824642340938607479) ^ 117806048705515354 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 824642340938607479) ^ 413769363240646 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 824642340938607479) ^ 853109760538 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 824642340938607479) ^ 26970938162 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_913439945994369499 : Nat.Prime 913439945994369499 := by
  apply lucas_primality 913439945994369499 (3 : ZMod 913439945994369499)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (3037267, 1), (1856444687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (3037267, 1), (1856444687, 1)] : List FactorBlock).map factorBlockValue).prod) = 913439945994369499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_3037267
      · exact prime_oneHundredThirtySevenEE_1856444687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 913439945994369499) ^ 456719972997184749 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439945994369499) ^ 304479981998123166 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439945994369499) ^ 300744039294 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 913439945994369499) ^ 492037254 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1026015923032231633 : Nat.Prime 1026015923032231633 := by
  apply lucas_primality 1026015923032231633 (7 : ZMod 1026015923032231633)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (53, 1), (30391, 1), (308619631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (53, 1), (30391, 1), (308619631, 1)] : List FactorBlock).map factorBlockValue).prod) = 1026015923032231633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_43
      · exact prime_oneHundredThirtySevenEE_53
      · exact prime_oneHundredThirtySevenEE_30391
      · exact prime_oneHundredThirtySevenEE_308619631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1026015923032231633) ^ 513007961516115816 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1026015923032231633) ^ 342005307677410544 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1026015923032231633) ^ 23860835419354224 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1026015923032231633) ^ 19358791000608144 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1026015923032231633) ^ 33760518674352 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1026015923032231633) ^ 3324532272 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1267894217814040763 : Nat.Prime 1267894217814040763 := by
  apply lucas_primality 1267894217814040763 (2 : ZMod 1267894217814040763)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (4583, 1), (12575072082737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (4583, 1), (12575072082737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1267894217814040763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_4583
      · exact prime_oneHundredThirtySevenEE_12575072082737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1267894217814040763) ^ 633947108907020381 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267894217814040763) ^ 115263110710367342 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267894217814040763) ^ 276651585820214 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1267894217814040763) ^ 100826 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1352843132339974081 : Nat.Prime 1352843132339974081 := by
  apply lucas_primality 1352843132339974081 (34 : ZMod 1352843132339974081)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (13, 1), (8563, 1), (25717, 1), (492251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (13, 1), (8563, 1), (25717, 1), (492251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1352843132339974081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_8563
      · exact prime_oneHundredThirtySevenEE_25717
      · exact prime_oneHundredThirtySevenEE_492251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (34 : ZMod 1352843132339974081) ^ 676421566169987040 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 450947710779991360 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 270568626467994816 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 104064856333844160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 157987052708160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 52605013506240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (34 : ZMod 1352843132339974081) ^ 2748279094080 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1541984099181347231 : Nat.Prime 1541984099181347231 := by
  apply lucas_primality 1541984099181347231 (7 : ZMod 1541984099181347231)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (751, 1), (697691, 1), (946273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (751, 1), (697691, 1), (946273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1541984099181347231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_311
      · exact prime_oneHundredThirtySevenEE_751
      · exact prime_oneHundredThirtySevenEE_697691
      · exact prime_oneHundredThirtySevenEE_946273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1541984099181347231) ^ 770992049590673615 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1541984099181347231) ^ 308396819836269446 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1541984099181347231) ^ 4958148228878930 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1541984099181347231) ^ 2053241144049730 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1541984099181347231) ^ 2210124681530 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1541984099181347231) ^ 1629534076510 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2045482207736893733 : Nat.Prime 2045482207736893733 := by
  apply lucas_primality 2045482207736893733 (2 : ZMod 2045482207736893733)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (511370551934223433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (511370551934223433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2045482207736893733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_511370551934223433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2045482207736893733) ^ 1022741103868446866 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 2045482207736893733) ^ 4 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2590807218358065331 : Nat.Prime 2590807218358065331 := by
  apply lucas_primality 2590807218358065331 (7 : ZMod 2590807218358065331)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (6643095431687347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (6643095431687347, 1)] : List FactorBlock).map factorBlockValue).prod) = 2590807218358065331 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_6643095431687347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2590807218358065331) ^ 1295403609179032665 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2590807218358065331) ^ 863602406119355110 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2590807218358065331) ^ 518161443671613066 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2590807218358065331) ^ 199292862950620410 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 2590807218358065331) ^ 390 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3764727327801072299 : Nat.Prime 3764727327801072299 := by
  apply lucas_primality 3764727327801072299 (2 : ZMod 3764727327801072299)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (173, 1), (19249, 1), (565261302937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (173, 1), (19249, 1), (565261302937, 1)] : List FactorBlock).map factorBlockValue).prod) = 3764727327801072299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_173
      · exact prime_oneHundredThirtySevenEE_19249
      · exact prime_oneHundredThirtySevenEE_565261302937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3764727327801072299) ^ 1882363663900536149 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764727327801072299) ^ 21761429640468626 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764727327801072299) ^ 195580410816202 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 3764727327801072299) ^ 6660154 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_6632695747601761687 : Nat.Prime 6632695747601761687 := by
  apply lucas_primality 6632695747601761687 (3 : ZMod 6632695747601761687)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (317, 1), (1721, 1), (9661, 1), (209737753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (317, 1), (1721, 1), (9661, 1), (209737753, 1)] : List FactorBlock).map factorBlockValue).prod) = 6632695747601761687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_317
      · exact prime_oneHundredThirtySevenEE_1721
      · exact prime_oneHundredThirtySevenEE_9661
      · exact prime_oneHundredThirtySevenEE_209737753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6632695747601761687) ^ 3316347873800880843 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6632695747601761687) ^ 2210898582533920562 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6632695747601761687) ^ 20923330434074958 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6632695747601761687) ^ 3853977773156166 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6632695747601761687) ^ 686543395880526 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 6632695747601761687) ^ 31623757062 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_8033398566172081273 : Nat.Prime 8033398566172081273 := by
  apply lucas_primality 8033398566172081273 (5 : ZMod 8033398566172081273)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (111574980085723351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (111574980085723351, 1)] : List FactorBlock).map factorBlockValue).prod) = 8033398566172081273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_111574980085723351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 8033398566172081273) ^ 4016699283086040636 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8033398566172081273) ^ 2677799522057360424 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 8033398566172081273) ^ 72 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_14005259466900729479 : Nat.Prime 14005259466900729479 := by
  apply lucas_primality 14005259466900729479 (7 : ZMod 14005259466900729479)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (27067, 1), (27941, 1), (841756367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (27067, 1), (27941, 1), (841756367, 1)] : List FactorBlock).map factorBlockValue).prod) = 14005259466900729479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_27067
      · exact prime_oneHundredThirtySevenEE_27941
      · exact prime_oneHundredThirtySevenEE_841756367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 14005259466900729479) ^ 7002629733450364739 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14005259466900729479) ^ 1273205406081884498 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14005259466900729479) ^ 517429322307634 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14005259466900729479) ^ 501244030882958 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 14005259466900729479) ^ 16638139034 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_17580285029646009323 : Nat.Prime 17580285029646009323 := by
  apply lucas_primality 17580285029646009323 (2 : ZMod 17580285029646009323)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (41, 1), (101, 1), (349, 1), (16883, 1), (12422747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (41, 1), (101, 1), (349, 1), (16883, 1), (12422747, 1)] : List FactorBlock).map factorBlockValue).prod) = 17580285029646009323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_29
      · exact prime_oneHundredThirtySevenEE_41
      · exact prime_oneHundredThirtySevenEE_101
      · exact prime_oneHundredThirtySevenEE_349
      · exact prime_oneHundredThirtySevenEE_16883
      · exact prime_oneHundredThirtySevenEE_12422747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17580285029646009323) ^ 8790142514823004661 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 606216725160207218 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 428787439747463642 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 174062228016297122 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 50373309540532978 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 1041301014609134 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 17580285029646009323) ^ 1415168885726 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_19033722086362484047 : Nat.Prime 19033722086362484047 := by
  apply lucas_primality 19033722086362484047 (5 : ZMod 19033722086362484047)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (89, 1), (5575861, 1), (10035317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (89, 1), (5575861, 1), (10035317, 1)] : List FactorBlock).map factorBlockValue).prod) = 19033722086362484047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_89
      · exact prime_oneHundredThirtySevenEE_5575861
      · exact prime_oneHundredThirtySevenEE_10035317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19033722086362484047) ^ 9516861043181242023 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 6344574028787494682 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 2719103155194640578 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 1464132468181729542 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 213862045914185214 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 3413593360086 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 19033722086362484047) ^ 1896673726038 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_40973068694686188479 : Nat.Prime 40973068694686188479 := by
  apply lucas_primality 40973068694686188479 (11 : ZMod 40973068694686188479)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (109553659611460397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (109553659611460397, 1)] : List FactorBlock).map factorBlockValue).prod) = 40973068694686188479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_11
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_109553659611460397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 40973068694686188479) ^ 20486534347343094239 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 40973068694686188479) ^ 3724824426789653498 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 40973068694686188479) ^ 2410180511452128734 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (11 : ZMod 40973068694686188479) ^ 374 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_64047557998729087087 : Nat.Prime 64047557998729087087 := by
  apply lucas_primality 64047557998729087087 (3 : ZMod 64047557998729087087)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (9227, 1), (1156886637020503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (9227, 1), (1156886637020503, 1)] : List FactorBlock).map factorBlockValue).prod) = 64047557998729087087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_9227
      · exact prime_oneHundredThirtySevenEE_1156886637020503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 64047557998729087087) ^ 32023778999364543543 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64047557998729087087) ^ 21349185999576362362 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64047557998729087087) ^ 6941319822123018 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 64047557998729087087) ^ 55362 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_65424775946616105347 : Nat.Prime 65424775946616105347 := by
  apply lucas_primality 65424775946616105347 (2 : ZMod 65424775946616105347)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (149, 1), (10169, 1), (164807297143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (149, 1), (10169, 1), (164807297143, 1)] : List FactorBlock).map factorBlockValue).prod) = 65424775946616105347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_131
      · exact prime_oneHundredThirtySevenEE_149
      · exact prime_oneHundredThirtySevenEE_10169
      · exact prime_oneHundredThirtySevenEE_164807297143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65424775946616105347) ^ 32712387973308052673 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65424775946616105347) ^ 499425770584855766 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65424775946616105347) ^ 439092456017557754 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65424775946616105347) ^ 6433747265868434 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 65424775946616105347) ^ 396977422 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_77508049263126868021 : Nat.Prime 77508049263126868021 := by
  apply lucas_primality 77508049263126868021 (2 : ZMod 77508049263126868021)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17, 2), (617, 1), (7244568938059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17, 2), (617, 1), (7244568938059, 1)] : List FactorBlock).map factorBlockValue).prod) = 77508049263126868021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_617
      · exact prime_oneHundredThirtySevenEE_7244568938059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 77508049263126868021) ^ 38754024631563434010 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77508049263126868021) ^ 25836016421042289340 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77508049263126868021) ^ 15501609852625373604 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77508049263126868021) ^ 4559297015478051060 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77508049263126868021) ^ 125620825385943060 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 77508049263126868021) ^ 10698780 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_83203455652285784833 : Nat.Prime 83203455652285784833 := by
  apply lucas_primality 83203455652285784833 (5 : ZMod 83203455652285784833)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 4), (4012512328910387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 4), (4012512328910387, 1)] : List FactorBlock).map factorBlockValue).prod) = 83203455652285784833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_4012512328910387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 83203455652285784833) ^ 41601727826142892416 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 83203455652285784833) ^ 27734485217428594944 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 83203455652285784833) ^ 20736 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_100915252565274416701 : Nat.Prime 100915252565274416701 := by
  apply lucas_primality 100915252565274416701 (2 : ZMod 100915252565274416701)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (131, 1), (5281, 1), (16921, 1), (9578573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (131, 1), (5281, 1), (16921, 1), (9578573, 1)] : List FactorBlock).map factorBlockValue).prod) = 100915252565274416701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_131
      · exact prime_oneHundredThirtySevenEE_5281
      · exact prime_oneHundredThirtySevenEE_16921
      · exact prime_oneHundredThirtySevenEE_9578573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100915252565274416701) ^ 50457626282637208350 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 33638417521758138900 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 20183050513054883340 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 770345439429575700 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 19109118077120700 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 5963905949132700 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 100915252565274416701) ^ 10535520537900 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_319609819987516598399 : Nat.Prime 319609819987516598399 := by
  apply lucas_primality 319609819987516598399 (13 : ZMod 319609819987516598399)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (39359, 1), (40199873767661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (39359, 1), (40199873767661, 1)] : List FactorBlock).map factorBlockValue).prod) = 319609819987516598399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_101
      · exact prime_oneHundredThirtySevenEE_39359
      · exact prime_oneHundredThirtySevenEE_40199873767661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 319609819987516598399) ^ 159804909993758299199 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 319609819987516598399) ^ 3164453663242738598 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 319609819987516598399) ^ 8120374501067522 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (13 : ZMod 319609819987516598399) ^ 7950518 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_437133095680663070519 : Nat.Prime 437133095680663070519 := by
  apply lucas_primality 437133095680663070519 (17 : ZMod 437133095680663070519)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43261, 1), (5052276827635319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43261, 1), (5052276827635319, 1)] : List FactorBlock).map factorBlockValue).prod) = 437133095680663070519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_43261
      · exact prime_oneHundredThirtySevenEE_5052276827635319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 437133095680663070519) ^ 218566547840331535259 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 437133095680663070519) ^ 10104553655270638 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (17 : ZMod 437133095680663070519) ^ 86522 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_491676824336234261749 : Nat.Prime 491676824336234261749 := by
  apply lucas_primality 491676824336234261749 (2 : ZMod 491676824336234261749)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (40973068694686188479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (40973068694686188479, 1)] : List FactorBlock).map factorBlockValue).prod) = 491676824336234261749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_40973068694686188479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 491676824336234261749) ^ 245838412168117130874 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 491676824336234261749) ^ 163892274778744753916 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 491676824336234261749) ^ 12 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_598939408431953616481 : Nat.Prime 598939408431953616481 := by
  apply lucas_primality 598939408431953616481 (31 : ZMod 598939408431953616481)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (17, 1), (73399437307837453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (17, 1), (73399437307837453, 1)] : List FactorBlock).map factorBlockValue).prod) = 598939408431953616481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_73399437307837453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 598939408431953616481) ^ 299469704215976808240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (31 : ZMod 598939408431953616481) ^ 199646469477317872160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (31 : ZMod 598939408431953616481) ^ 119787881686390723296 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (31 : ZMod 598939408431953616481) ^ 35231729907761977440 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (31 : ZMod 598939408431953616481) ^ 8160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_834631923175908650851 : Nat.Prime 834631923175908650851 := by
  apply lucas_primality 834631923175908650851 (2 : ZMod 834631923175908650851)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (198294401, 1), (28060362739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (198294401, 1), (28060362739, 1)] : List FactorBlock).map factorBlockValue).prod) = 834631923175908650851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_198294401
      · exact prime_oneHundredThirtySevenEE_28060362739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 834631923175908650851) ^ 417315961587954325425 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 834631923175908650851) ^ 278210641058636216950 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 834631923175908650851) ^ 166926384635181730170 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 834631923175908650851) ^ 4209054410850 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 834631923175908650851) ^ 29744160150 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1172037367623258473321 : Nat.Prime 1172037367623258473321 := by
  apply lucas_primality 1172037367623258473321 (3 : ZMod 1172037367623258473321)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (340079, 1), (86159198864327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (340079, 1), (86159198864327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1172037367623258473321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_340079
      · exact prime_oneHundredThirtySevenEE_86159198864327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1172037367623258473321) ^ 586018683811629236660 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172037367623258473321) ^ 234407473524651694664 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172037367623258473321) ^ 3446367954573080 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1172037367623258473321) ^ 13603160 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1846422726258775508381 : Nat.Prime 1846422726258775508381 := by
  apply lucas_primality 1846422726258775508381 (2 : ZMod 1846422726258775508381)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13505501, 1), (6835817220919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13505501, 1), (6835817220919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1846422726258775508381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_13505501
      · exact prime_oneHundredThirtySevenEE_6835817220919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1846422726258775508381) ^ 923211363129387754190 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1846422726258775508381) ^ 369284545251755101676 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1846422726258775508381) ^ 136716344418380 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1846422726258775508381) ^ 270110020 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_3255338069051328456883 : Nat.Prime 3255338069051328456883 := by
  apply lucas_primality 3255338069051328456883 (5 : ZMod 3255338069051328456883)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (77508049263126868021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (77508049263126868021, 1)] : List FactorBlock).map factorBlockValue).prod) = 3255338069051328456883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_77508049263126868021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3255338069051328456883) ^ 1627669034525664228441 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3255338069051328456883) ^ 1085112689683776152294 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3255338069051328456883) ^ 465048295578761208126 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 3255338069051328456883) ^ 42 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_4759356777741446162687 : Nat.Prime 4759356777741446162687 := by
  apply lucas_primality 4759356777741446162687 (10 : ZMod 4759356777741446162687)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (89, 1), (1727391737, 1), (15478804751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (89, 1), (1727391737, 1), (15478804751, 1)] : List FactorBlock).map factorBlockValue).prod) = 4759356777741446162687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_89
      · exact prime_oneHundredThirtySevenEE_1727391737
      · exact prime_oneHundredThirtySevenEE_15478804751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4759356777741446162687) ^ 2379678388870723081343 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4759356777741446162687) ^ 53475918851027484974 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4759356777741446162687) ^ 2755227245678 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 4759356777741446162687) ^ 307475729186 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_5354573490450305686637 : Nat.Prime 5354573490450305686637 := by
  apply lucas_primality 5354573490450305686637 (2 : ZMod 5354573490450305686637)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (388231, 1), (3448058945866189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (388231, 1), (3448058945866189, 1)] : List FactorBlock).map factorBlockValue).prod) = 5354573490450305686637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_388231
      · exact prime_oneHundredThirtySevenEE_3448058945866189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5354573490450305686637) ^ 2677286745225152843318 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5354573490450305686637) ^ 13792235783464756 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 5354573490450305686637) ^ 1552924 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_10483635412188008888959 : Nat.Prime 10483635412188008888959 := by
  apply lucas_primality 10483635412188008888959 (3 : ZMod 10483635412188008888959)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (83203455652285784833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (83203455652285784833, 1)] : List FactorBlock).map factorBlockValue).prod) = 10483635412188008888959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_83203455652285784833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10483635412188008888959) ^ 5241817706094004444479 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10483635412188008888959) ^ 3494545137396002962986 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10483635412188008888959) ^ 1497662201741144126994 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 10483635412188008888959) ^ 126 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_11965397694401885304047 : Nat.Prime 11965397694401885304047 := by
  apply lucas_primality 11965397694401885304047 (5 : ZMod 11965397694401885304047)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (17, 1), (1026015923032231633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (17, 1), (1026015923032231633, 1)] : List FactorBlock).map factorBlockValue).prod) = 11965397694401885304047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_1026015923032231633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11965397694401885304047) ^ 5982698847200942652023 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 11965397694401885304047) ^ 1709342527771697900578 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 11965397694401885304047) ^ 703846923200110900238 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 11965397694401885304047) ^ 11662 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_13746096979373090584831 : Nat.Prime 13746096979373090584831 := by
  apply lucas_primality 13746096979373090584831 (3 : ZMod 13746096979373090584831)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (293, 1), (302513, 1), (5169475554829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (293, 1), (302513, 1), (5169475554829, 1)] : List FactorBlock).map factorBlockValue).prod) = 13746096979373090584831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_293
      · exact prime_oneHundredThirtySevenEE_302513
      · exact prime_oneHundredThirtySevenEE_5169475554829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13746096979373090584831) ^ 6873048489686545292415 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13746096979373090584831) ^ 4582032326457696861610 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13746096979373090584831) ^ 2749219395874618116966 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13746096979373090584831) ^ 46915006755539558310 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13746096979373090584831) ^ 45439690126946910 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 13746096979373090584831) ^ 2659089270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_23547664718894703264991 : Nat.Prime 23547664718894703264991 := by
  apply lucas_primality 23547664718894703264991 (3 : ZMod 23547664718894703264991)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (53993, 1), (654413, 1), (3173504891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (53993, 1), (654413, 1), (3173504891, 1)] : List FactorBlock).map factorBlockValue).prod) = 23547664718894703264991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_53993
      · exact prime_oneHundredThirtySevenEE_654413
      · exact prime_oneHundredThirtySevenEE_3173504891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 23547664718894703264991) ^ 11773832359447351632495 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 7849221572964901088330 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 4709532943778940652998 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 3363952102699243323570 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 436124399809136430 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 35982880411750230 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 23547664718894703264991) ^ 7420081432890 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_33020087633724911144339 : Nat.Prime 33020087633724911144339 := by
  apply lucas_primality 33020087633724911144339 (2 : ZMod 33020087633724911144339)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137707, 1), (119892553151709467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137707, 1), (119892553151709467, 1)] : List FactorBlock).map factorBlockValue).prod) = 33020087633724911144339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_137707
      · exact prime_oneHundredThirtySevenEE_119892553151709467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 33020087633724911144339) ^ 16510043816862455572169 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33020087633724911144339) ^ 239785106303418934 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 33020087633724911144339) ^ 275414 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_47831344119613875550657 : Nat.Prime 47831344119613875550657 := by
  apply lucas_primality 47831344119613875550657 (10 : ZMod 47831344119613875550657)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (389, 1), (640415382921136937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (389, 1), (640415382921136937, 1)] : List FactorBlock).map factorBlockValue).prod) = 47831344119613875550657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_389
      · exact prime_oneHundredThirtySevenEE_640415382921136937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 47831344119613875550657) ^ 23915672059806937775328 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 47831344119613875550657) ^ 15943781373204625183552 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 47831344119613875550657) ^ 122959753520858291904 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 47831344119613875550657) ^ 74688 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_90448400208675953591011 : Nat.Prime 90448400208675953591011 := by
  apply lucas_primality 90448400208675953591011 (2 : ZMod 90448400208675953591011)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (431, 1), (259082811173200291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (431, 1), (259082811173200291, 1)] : List FactorBlock).map factorBlockValue).prod) = 90448400208675953591011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_431
      · exact prime_oneHundredThirtySevenEE_259082811173200291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 90448400208675953591011) ^ 45224200104337976795505 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90448400208675953591011) ^ 30149466736225317863670 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90448400208675953591011) ^ 18089680041735190718202 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90448400208675953591011) ^ 209857077050292235710 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 90448400208675953591011) ^ 349110 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_112571882302142710493159 : Nat.Prime 112571882302142710493159 := by
  apply lucas_primality 112571882302142710493159 (7 : ZMod 112571882302142710493159)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (688959857, 1), (11670997452421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (688959857, 1), (11670997452421, 1)] : List FactorBlock).map factorBlockValue).prod) = 112571882302142710493159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_688959857
      · exact prime_oneHundredThirtySevenEE_11670997452421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 112571882302142710493159) ^ 56285941151071355246579 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 112571882302142710493159) ^ 16081697471734672927594 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 112571882302142710493159) ^ 163393964333894 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 112571882302142710493159) ^ 9645437998 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_427707160438048225007081 : Nat.Prime 427707160438048225007081 := by
  apply lucas_primality 427707160438048225007081 (3 : ZMod 427707160438048225007081)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (23893, 1), (23553868477116631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (23893, 1), (23553868477116631, 1)] : List FactorBlock).map factorBlockValue).prod) = 427707160438048225007081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_23893
      · exact prime_oneHundredThirtySevenEE_23553868477116631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 427707160438048225007081) ^ 213853580219024112503540 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 427707160438048225007081) ^ 85541432087609645001416 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 427707160438048225007081) ^ 22510903180949906579320 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 427707160438048225007081) ^ 17900940042608639560 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 427707160438048225007081) ^ 18158680 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1036677951370242399955559 : Nat.Prime 1036677951370242399955559 := by
  apply lucas_primality 1036677951370242399955559 (7 : ZMod 1036677951370242399955559)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (571, 1), (8033398566172081273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (571, 1), (8033398566172081273, 1)] : List FactorBlock).map factorBlockValue).prod) = 1036677951370242399955559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_113
      · exact prime_oneHundredThirtySevenEE_571
      · exact prime_oneHundredThirtySevenEE_8033398566172081273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1036677951370242399955559) ^ 518338975685121199977779 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1036677951370242399955559) ^ 9174141162568516813766 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1036677951370242399955559) ^ 1815548075954890367698 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (7 : ZMod 1036677951370242399955559) ^ 129046 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1294697674093240550338973 : Nat.Prime 1294697674093240550338973 := by
  apply lucas_primality 1294697674093240550338973 (2 : ZMod 1294697674093240550338973)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (349, 1), (751, 1), (94994762261972689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (349, 1), (751, 1), (94994762261972689, 1)] : List FactorBlock).map factorBlockValue).prod) = 1294697674093240550338973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_349
      · exact prime_oneHundredThirtySevenEE_751
      · exact prime_oneHundredThirtySevenEE_94994762261972689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1294697674093240550338973) ^ 647348837046620275169486 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294697674093240550338973) ^ 99592128776403119256844 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294697674093240550338973) ^ 3709735455854557450828 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294697674093240550338973) ^ 1723964945530280359972 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1294697674093240550338973) ^ 13629148 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_17851930246014181920980551 : Nat.Prime 17851930246014181920980551 := by
  apply lucas_primality 17851930246014181920980551 (3 : ZMod 17851930246014181920980551)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (19, 1), (4289, 1), (486813956170052369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (19, 1), (4289, 1), (486813956170052369, 1)] : List FactorBlock).map factorBlockValue).prod) = 17851930246014181920980551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_19
      · exact prime_oneHundredThirtySevenEE_4289
      · exact prime_oneHundredThirtySevenEE_486813956170052369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17851930246014181920980551) ^ 8925965123007090960490275 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17851930246014181920980551) ^ 5950643415338060640326850 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17851930246014181920980551) ^ 3570386049202836384196110 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17851930246014181920980551) ^ 939575276106009574788450 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17851930246014181920980551) ^ 4162259325253947754950 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 17851930246014181920980551) ^ 36670950 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_27022115969650762857700457 : Nat.Prime 27022115969650762857700457 := by
  apply lucas_primality 27022115969650762857700457 (3 : ZMod 27022115969650762857700457)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (35671, 1), (187931, 1), (503866700050657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (35671, 1), (187931, 1), (503866700050657, 1)] : List FactorBlock).map factorBlockValue).prod) = 27022115969650762857700457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_35671
      · exact prime_oneHundredThirtySevenEE_187931
      · exact prime_oneHundredThirtySevenEE_503866700050657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 27022115969650762857700457) ^ 13511057984825381428850228 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 27022115969650762857700457) ^ 757537382457760165336 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 27022115969650762857700457) ^ 143787432460055886776 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 27022115969650762857700457) ^ 53629493608 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_37191862944221968442952133 : Nat.Prime 37191862944221968442952133 := by
  apply lucas_primality 37191862944221968442952133 (2 : ZMod 37191862944221968442952133)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (293, 1), (359, 1), (133699619, 1), (220381151587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (293, 1), (359, 1), (133699619, 1), (220381151587, 1)] : List FactorBlock).map factorBlockValue).prod) = 37191862944221968442952133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_293
      · exact prime_oneHundredThirtySevenEE_359
      · exact prime_oneHundredThirtySevenEE_133699619
      · exact prime_oneHundredThirtySevenEE_220381151587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37191862944221968442952133) ^ 18595931472110984221476066 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37191862944221968442952133) ^ 12397287648073989480984044 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37191862944221968442952133) ^ 126934685816457230180724 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37191862944221968442952133) ^ 103598504022902419061148 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37191862944221968442952133) ^ 278174786303781228 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 37191862944221968442952133) ^ 168761541885036 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_145134913191833935993778261 : Nat.Prime 145134913191833935993778261 := by
  apply lucas_primality 145134913191833935993778261 (10 : ZMod 145134913191833935993778261)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1036677951370242399955559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1036677951370242399955559, 1)] : List FactorBlock).map factorBlockValue).prod) = 145134913191833935993778261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_1036677951370242399955559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 145134913191833935993778261) ^ 72567456595916967996889130 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 145134913191833935993778261) ^ 29026982638366787198755652 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 145134913191833935993778261) ^ 20733559027404847999111180 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (10 : ZMod 145134913191833935993778261) ^ 140 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_219472307753504976380835419 : Nat.Prime 219472307753504976380835419 := by
  apply lucas_primality 219472307753504976380835419 (2 : ZMod 219472307753504976380835419)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1087409, 1), (100915252565274416701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1087409, 1), (100915252565274416701, 1)] : List FactorBlock).map factorBlockValue).prod) = 219472307753504976380835419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_1087409
      · exact prime_oneHundredThirtySevenEE_100915252565274416701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 219472307753504976380835419) ^ 109736153876752488190417709 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 219472307753504976380835419) ^ 201830505130548833402 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 219472307753504976380835419) ^ 2174818 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_266398952503432027251737729 : Nat.Prime 266398952503432027251737729 := by
  apply lucas_primality 266398952503432027251737729 (6 : ZMod 266398952503432027251737729)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (17, 1), (396887, 1), (531811613, 1), (580027963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (17, 1), (396887, 1), (531811613, 1), (580027963, 1)] : List FactorBlock).map factorBlockValue).prod) = 266398952503432027251737729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_17
      · exact prime_oneHundredThirtySevenEE_396887
      · exact prime_oneHundredThirtySevenEE_531811613
      · exact prime_oneHundredThirtySevenEE_580027963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 266398952503432027251737729) ^ 133199476251716013625868864 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 266398952503432027251737729) ^ 15670526617848942779513984 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 266398952503432027251737729) ^ 671221159935780278144 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 266398952503432027251737729) ^ 500927294536969856 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (6 : ZMod 266398952503432027251737729) ^ 459286395651638656 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_359136503596644506805003413 : Nat.Prime 359136503596644506805003413 := by
  apply lucas_primality 359136503596644506805003413 (2 : ZMod 359136503596644506805003413)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (23, 1), (193, 1), (1009, 1), (1541984099181347231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (23, 1), (193, 1), (1009, 1), (1541984099181347231, 1)] : List FactorBlock).map factorBlockValue).prod) = 359136503596644506805003413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_13
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_193
      · exact prime_oneHundredThirtySevenEE_1009
      · exact prime_oneHundredThirtySevenEE_1541984099181347231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 359136503596644506805003413) ^ 179568251798322253402501706 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 359136503596644506805003413) ^ 27625884892049577446538724 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 359136503596644506805003413) ^ 15614630591158456817608844 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 359136503596644506805003413) ^ 1860810899464479309870484 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 359136503596644506805003413) ^ 355933105645832018637268 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 359136503596644506805003413) ^ 232905452 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_645301048295166026171539997 : Nat.Prime 645301048295166026171539997 := by
  apply lucas_primality 645301048295166026171539997 (2 : ZMod 645301048295166026171539997)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (223, 1), (1553, 1), (610871419, 1), (33154953133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (223, 1), (1553, 1), (610871419, 1), (33154953133, 1)] : List FactorBlock).map factorBlockValue).prod) = 645301048295166026171539997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_23
      · exact prime_oneHundredThirtySevenEE_223
      · exact prime_oneHundredThirtySevenEE_1553
      · exact prime_oneHundredThirtySevenEE_610871419
      · exact prime_oneHundredThirtySevenEE_33154953133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 645301048295166026171539997) ^ 322650524147583013085769998 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 645301048295166026171539997) ^ 28056567317181131572675652 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 645301048295166026171539997) ^ 2893726673969354377450852 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 645301048295166026171539997) ^ 415519026590576964695132 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 645301048295166026171539997) ^ 1056361499694203284 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 645301048295166026171539997) ^ 19463186864012812 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_771288395819460345566935901 : Nat.Prime 771288395819460345566935901 := by
  apply lucas_primality 771288395819460345566935901 (2 : ZMod 771288395819460345566935901)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (218381377, 1), (35318414345352367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (218381377, 1), (35318414345352367, 1)] : List FactorBlock).map factorBlockValue).prod) = 771288395819460345566935901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_218381377
      · exact prime_oneHundredThirtySevenEE_35318414345352367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 771288395819460345566935901) ^ 385644197909730172783467950 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 771288395819460345566935901) ^ 154257679163892069113387180 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 771288395819460345566935901) ^ 3531841434535236700 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 771288395819460345566935901) ^ 21838137700 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1361097169093165315706357473 : Nat.Prime 1361097169093165315706357473 := by
  apply lucas_primality 1361097169093165315706357473 (5 : ZMod 1361097169093165315706357473)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (359, 1), (16476535487, 1), (798980713943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (359, 1), (16476535487, 1), (798980713943, 1)] : List FactorBlock).map factorBlockValue).prod) = 1361097169093165315706357473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_359
      · exact prime_oneHundredThirtySevenEE_16476535487
      · exact prime_oneHundredThirtySevenEE_798980713943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1361097169093165315706357473) ^ 680548584546582657853178736 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361097169093165315706357473) ^ 453699056364388438568785824 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361097169093165315706357473) ^ 3791357016972605336229408 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361097169093165315706357473) ^ 82608213975994656 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 1361097169093165315706357473) ^ 1703541957071904 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1499727436315617338602375363 : Nat.Prime 1499727436315617338602375363 := by
  apply lucas_primality 1499727436315617338602375363 (2 : ZMod 1499727436315617338602375363)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (397, 1), (3917, 1), (4649, 1), (10795871, 1), (3202578437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (397, 1), (3917, 1), (4649, 1), (10795871, 1), (3202578437, 1)] : List FactorBlock).map factorBlockValue).prod) = 1499727436315617338602375363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_397
      · exact prime_oneHundredThirtySevenEE_3917
      · exact prime_oneHundredThirtySevenEE_4649
      · exact prime_oneHundredThirtySevenEE_10795871
      · exact prime_oneHundredThirtySevenEE_3202578437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1499727436315617338602375363) ^ 749863718157808669301187681 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 499909145438539112867458454 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 3777650973087197326454346 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 382876547438247980240586 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 322591403810629670596338 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 138916761446632452222 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 1499727436315617338602375363) ^ 468287495784328026 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_1840574580932803097375642491 : Nat.Prime 1840574580932803097375642491 := by
  apply lucas_primality 1840574580932803097375642491 (3 : ZMod 1840574580932803097375642491)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (541, 1), (1187, 1), (3215879, 1), (29708756996531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (541, 1), (1187, 1), (3215879, 1), (29708756996531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1840574580932803097375642491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_541
      · exact prime_oneHundredThirtySevenEE_1187
      · exact prime_oneHundredThirtySevenEE_3215879
      · exact prime_oneHundredThirtySevenEE_29708756996531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1840574580932803097375642491) ^ 920287290466401548687821245 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 613524860310934365791880830 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 368114916186560619475128498 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 3402171129265809791821890 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 1550610430440440688606270 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 572339500625739680310 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 1840574580932803097375642491) ^ 61953941093790 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_2745263781730282585916212529 : Nat.Prime 2745263781730282585916212529 := by
  apply lucas_primality 2745263781730282585916212529 (3 : ZMod 2745263781730282585916212529)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (11257, 1), (491676824336234261749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (11257, 1), (491676824336234261749, 1)] : List FactorBlock).map factorBlockValue).prod) = 2745263781730282585916212529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_31
      · exact prime_oneHundredThirtySevenEE_11257
      · exact prime_oneHundredThirtySevenEE_491676824336234261749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2745263781730282585916212529) ^ 1372631890865141292958106264 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2745263781730282585916212529) ^ 88556896184847825352135888 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2745263781730282585916212529) ^ 243871704870772193827504 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 2745263781730282585916212529) ^ 5583472 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_7362298323731212389502569967 : Nat.Prime 7362298323731212389502569967 := by
  apply lucas_primality 7362298323731212389502569967 (5 : ZMod 7362298323731212389502569967)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (121171, 1), (1209325529, 1), (1196250708097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (121171, 1), (1209325529, 1), (1196250708097, 1)] : List FactorBlock).map factorBlockValue).prod) = 7362298323731212389502569967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_3
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_121171
      · exact prime_oneHundredThirtySevenEE_1209325529
      · exact prime_oneHundredThirtySevenEE_1196250708097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7362298323731212389502569967) ^ 3681149161865606194751284983 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7362298323731212389502569967) ^ 2454099441243737463167523322 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7362298323731212389502569967) ^ 1051756903390173198500367138 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7362298323731212389502569967) ^ 60759573856213222549146 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7362298323731212389502569967) ^ 6087937571134506654 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (5 : ZMod 7362298323731212389502569967) ^ 6154477714327278 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_8098528156104333628452826961 : Nat.Prime 8098528156104333628452826961 := by
  apply lucas_primality 8098528156104333628452826961 (3 : ZMod 8098528156104333628452826961)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (137, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (137, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8098528156104333628452826961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_137
      · exact prime_oneHundredThirtySevenEE_171401
      · exact prime_oneHundredThirtySevenEE_714027719
      · exact prime_oneHundredThirtySevenEE_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8098528156104333628452826961) ^ 4049264078052166814226413480 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8098528156104333628452826961) ^ 1619705631220866725690565392 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8098528156104333628452826961) ^ 59113344205141121375568080 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8098528156104333628452826961) ^ 47249013460273473482960 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8098528156104333628452826961) ^ 11342036087123297840 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 8098528156104333628452826961) ^ 1341340313104936240 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_11569325937291905183504038517 : Nat.Prime 11569325937291905183504038517 := by
  apply lucas_primality 11569325937291905183504038517 (3 : ZMod 11569325937291905183504038517)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (7129, 1), (2196763, 1), (26383852187426761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (7129, 1), (2196763, 1), (26383852187426761, 1)] : List FactorBlock).map factorBlockValue).prod) = 11569325937291905183504038517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_7
      · exact prime_oneHundredThirtySevenEE_7129
      · exact prime_oneHundredThirtySevenEE_2196763
      · exact prime_oneHundredThirtySevenEE_26383852187426761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11569325937291905183504038517) ^ 5784662968645952591752019258 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11569325937291905183504038517) ^ 1652760848184557883357719788 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11569325937291905183504038517) ^ 1622853967918628865690004 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11569325937291905183504038517) ^ 5266533502836630616732 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (3 : ZMod 11569325937291905183504038517) ^ 438500255956 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_32394112624417334513811307853 : Nat.Prime 32394112624417334513811307853 := by
  apply lucas_primality 32394112624417334513811307853 (2 : ZMod 32394112624417334513811307853)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (676829, 1), (11965397694401885304047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (676829, 1), (11965397694401885304047, 1)] : List FactorBlock).map factorBlockValue).prod) = 32394112624417334513811307853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_676829
      · exact prime_oneHundredThirtySevenEE_11965397694401885304047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32394112624417334513811307853) ^ 16197056312208667256905653926 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32394112624417334513811307853) ^ 47861590777607541216188 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (2 : ZMod 32394112624417334513811307853) ^ 2707316 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtySevenEE_80985281561043336284528269631 : Nat.Prime 80985281561043336284528269631 := by
  apply lucas_primality 80985281561043336284528269631 (23 : ZMod 80985281561043336284528269631)
  · rw [← oneHundredThirtySevenEEFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (676829, 1), (11965397694401885304047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (676829, 1), (11965397694401885304047, 1)] : List FactorBlock).map factorBlockValue).prod) = 80985281561043336284528269631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtySevenEE_2
      · exact prime_oneHundredThirtySevenEE_5
      · exact prime_oneHundredThirtySevenEE_676829
      · exact prime_oneHundredThirtySevenEE_11965397694401885304047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 80985281561043336284528269631) ^ 40492640780521668142264134815 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (23 : ZMod 80985281561043336284528269631) ^ 16197056312208667256905653926 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (23 : ZMod 80985281561043336284528269631) ^ 119653976944018853040470 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide
    · change (23 : ZMod 80985281561043336284528269631) ^ 6768290 ≠ 1
      rw [← oneHundredThirtySevenEEFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539200 : Nat.totient 161970563122086672569056539200 = 64314943161426548897255424000 := by
  rw [← show ((([(2, 6), (5, 2), (137, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_137, prime_oneHundredThirtySevenEE_171401, prime_oneHundredThirtySevenEE_714027719, prime_oneHundredThirtySevenEE_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539201 : Nat.totient 161970563122086672569056539201 = 106597536914520875477032466688 := by
  rw [← show ((([(3, 1), (79, 1), (6733, 1), (650669, 1), (155997994672005949, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_79, prime_oneHundredThirtySevenEE_6733, prime_oneHundredThirtySevenEE_650669, prime_oneHundredThirtySevenEE_155997994672005949]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539202 : Nat.totient 161970563122086672569056539202 = 70328802740341802489817246720 := by
  rw [← show ((([(2, 1), (13, 1), (17, 1), (2389, 1), (63894407219, 1), (2400683058491, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_2389, prime_oneHundredThirtySevenEE_63894407219, prime_oneHundredThirtySevenEE_2400683058491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539203 : Nat.totient 161970563122086672569056539203 = 132795662133261694305599435520 := by
  rw [← show ((([(7, 1), (23, 1), (1679683, 1), (598939408431953616481, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_23, prime_oneHundredThirtySevenEE_1679683, prime_oneHundredThirtySevenEE_598939408431953616481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539204 : Nat.totient 161970563122086672569056539204 = 53990187707362224189685513032 := by
  rw [← show ((([(2, 2), (3, 3), (1499727436315617338602375363, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_1499727436315617338602375363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539205 : Nat.totient 161970563122086672569056539205 = 129187555270284925020670202880 := by
  rw [← show ((([(5, 1), (389, 1), (2341, 1), (220757, 1), (161138972186560037, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_389, prime_oneHundredThirtySevenEE_2341, prime_oneHundredThirtySevenEE_220757, prime_oneHundredThirtySevenEE_161138972186560037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539206 : Nat.totient 161970563122086672569056539206 = 79110565559396938440927148480 := by
  rw [← show ((([(2, 1), (83, 1), (89, 1), (13294511, 1), (824642340938607479, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_83, prime_oneHundredThirtySevenEE_89, prime_oneHundredThirtySevenEE_13294511, prime_oneHundredThirtySevenEE_824642340938607479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539207 : Nat.totient 161970563122086672569056539207 = 107552501119166640980759424192 := by
  rw [← show ((([(3, 1), (263, 1), (6217, 1), (33020087633724911144339, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_263, prime_oneHundredThirtySevenEE_6217, prime_oneHundredThirtySevenEE_33020087633724911144339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539208 : Nat.totient 161970563122086672569056539208 = 73622983237312123895025699600 := by
  rw [← show ((([(2, 3), (11, 1), (1840574580932803097375642491, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_1840574580932803097375642491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539209 : Nat.totient 161970563122086672569056539209 = 160694774881318968357277933632 := by
  rw [← show ((([(127, 1), (374293, 1), (1100649967, 1), (3095789630357, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_127, prime_oneHundredThirtySevenEE_374293, prime_oneHundredThirtySevenEE_1100649967, prime_oneHundredThirtySevenEE_3095789630357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539210 : Nat.totient 161970563122086672569056539210 = 37021842999334096587212923200 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (7, 1), (771288395819460345566935901, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_771288395819460345566935901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539211 : Nat.totient 161970563122086672569056539211 = 159225299340356389983140326624 := by
  rw [← show ((([(59, 1), (2745263781730282585916212529, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_59, prime_oneHundredThirtySevenEE_2745263781730282585916212529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539212 : Nat.totient 161970563122086672569056539212 = 80985281245374970489256934912 := by
  rw [← show ((([(2, 2), (267807677, 1), (10903979887, 1), (13866537697, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_267807677, prime_oneHundredThirtySevenEE_10903979887, prime_oneHundredThirtySevenEE_13866537697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539213 : Nat.totient 161970563122086672569056539213 = 102297197644008588369972772992 := by
  rw [← show ((([(3, 2), (19, 2), (872029673, 1), (57168278901213269, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_19, prime_oneHundredThirtySevenEE_872029673, prime_oneHundredThirtySevenEE_57168278901213269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539214 : Nat.totient 161970563122086672569056539214 = 75670310502092730068663961600 := by
  rw [← show ((([(2, 1), (29, 1), (31, 1), (2488231, 1), (2717989739, 1), (13320112577, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_29, prime_oneHundredThirtySevenEE_31, prime_oneHundredThirtySevenEE_2488231, prime_oneHundredThirtySevenEE_2717989739, prime_oneHundredThirtySevenEE_13320112577]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539215 : Nat.totient 161970563122086672569056539215 = 117823821807295196027272354176 := by
  rw [← show ((([(5, 1), (13, 1), (67, 1), (37191862944221968442952133, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_67, prime_oneHundredThirtySevenEE_37191862944221968442952133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539216 : Nat.totient 161970563122086672569056539216 = 53338090947674606509471580160 := by
  rw [← show ((([(2, 4), (3, 1), (113, 1), (307, 1), (46189843877, 1), (2105869921081, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_113, prime_oneHundredThirtySevenEE_307, prime_oneHundredThirtySevenEE_46189843877, prime_oneHundredThirtySevenEE_2105869921081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539217 : Nat.totient 161970563122086672569056539217 = 138831906239711323146430218000 := by
  rw [← show ((([(7, 1), (27723181, 1), (834631923175908650851, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_27723181, prime_oneHundredThirtySevenEE_834631923175908650851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539218 : Nat.totient 161970563122086672569056539218 = 80957609245411811921637108480 := by
  rw [← show ((([(2, 1), (2927, 1), (20452007, 1), (1352843132339974081, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_2927, prime_oneHundredThirtySevenEE_20452007, prime_oneHundredThirtySevenEE_1352843132339974081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539219 : Nat.totient 161970563122086672569056539219 = 91975322767583808696080570880 := by
  rw [← show ((([(3, 1), (11, 1), (17, 1), (223, 1), (1294697674093240550338973, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_223, prime_oneHundredThirtySevenEE_1294697674093240550338973]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539220 : Nat.totient 161970563122086672569056539220 = 64788225248834669027622615680 := by
  rw [← show ((([(2, 2), (5, 1), (8098528156104333628452826961, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_8098528156104333628452826961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539221 : Nat.totient 161970563122086672569056539221 = 157443034587776794895730778800 := by
  rw [← show ((([(37, 2), (1051, 1), (112571882302142710493159, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_37, prime_oneHundredThirtySevenEE_1051, prime_oneHundredThirtySevenEE_112571882302142710493159]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539222 : Nat.totient 161970563122086672569056539222 = 52673353860841194331400500320 := by
  rw [← show ((([(2, 1), (3, 2), (41, 1), (219472307753504976380835419, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_41, prime_oneHundredThirtySevenEE_219472307753504976380835419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539223 : Nat.totient 161970563122086672569056539223 = 157454024769845084543048451000 := by
  rw [← show ((([(43, 1), (211, 1), (17851930246014181920980551, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_43, prime_oneHundredThirtySevenEE_211, prime_oneHundredThirtySevenEE_17851930246014181920980551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539224 : Nat.totient 161970563122086672569056539224 = 69406186905175386844902804480 := by
  rw [← show ((([(2, 3), (7, 2), (7129, 1), (2196763, 1), (26383852187426761, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_7129, prime_oneHundredThirtySevenEE_2196763, prime_oneHundredThirtySevenEE_26383852187426761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539225 : Nat.totient 161970563122086672569056539225 = 86079055453954258512929113920 := by
  rw [← show ((([(3, 1), (5, 2), (283, 1), (264975222059, 1), (28799379346259, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_283, prime_oneHundredThirtySevenEE_264975222059, prime_oneHundredThirtySevenEE_28799379346259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539226 : Nat.totient 161970563122086672569056539226 = 77464182349575948511604568208 := by
  rw [← show ((([(2, 1), (23, 1), (5885819189, 1), (598234346866585679, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_23, prime_oneHundredThirtySevenEE_5885819189, prime_oneHundredThirtySevenEE_598234346866585679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539227 : Nat.totient 161970563122086672569056539227 = 159505884499717611569729808000 := by
  rw [← show ((([(101, 1), (229, 1), (1171, 1), (6547, 1), (913439945994369499, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_101, prime_oneHundredThirtySevenEE_229, prime_oneHundredThirtySevenEE_1171, prime_oneHundredThirtySevenEE_6547, prime_oneHundredThirtySevenEE_913439945994369499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539228 : Nat.totient 161970563122086672569056539228 = 48776693775961338258487318272 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (47, 1), (1256573, 1), (17580285029646009323, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_47, prime_oneHundredThirtySevenEE_1256573, prime_oneHundredThirtySevenEE_17580285029646009323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539229 : Nat.totient 161970563122086672569056539229 = 161145225947220225023737331712 := by
  rw [← show ((([(277, 1), (673, 1), (200257, 1), (292243993, 1), (14845948849, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_277, prime_oneHundredThirtySevenEE_673, prime_oneHundredThirtySevenEE_200257, prime_oneHundredThirtySevenEE_292243993, prime_oneHundredThirtySevenEE_14845948849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539230 : Nat.totient 161970563122086672569056539230 = 58756563128287064789286961920 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (439, 1), (7673, 1), (437133095680663070519, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_439, prime_oneHundredThirtySevenEE_7673, prime_oneHundredThirtySevenEE_437133095680663070519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539231 : Nat.totient 161970563122086672569056539231 = 92464810596669945197682559872 := by
  rw [← show ((([(3, 3), (7, 1), (1117, 1), (17959, 1), (51719, 1), (826016733295447, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_1117, prime_oneHundredThirtySevenEE_17959, prime_oneHundredThirtySevenEE_51719, prime_oneHundredThirtySevenEE_826016733295447]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539232 : Nat.totient 161970563122086672569056539232 = 76722898320988423848500465664 := by
  rw [← show ((([(2, 5), (19, 1), (266398952503432027251737729, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_19, prime_oneHundredThirtySevenEE_266398952503432027251737729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539233 : Nat.totient 161970563122086672569056539233 = 158781308963685073989749662080 := by
  rw [← show ((([(53, 1), (1193, 1), (106623849671, 1), (24025111953187, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_53, prime_oneHundredThirtySevenEE_1193, prime_oneHundredThirtySevenEE_106623849671, prime_oneHundredThirtySevenEE_24025111953187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539234 : Nat.totient 161970563122086672569056539234 = 53989687406491216844221190160 := by
  rw [← show ((([(2, 1), (3, 1), (107923, 1), (1540175771, 1), (162405429905083, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_107923, prime_oneHundredThirtySevenEE_1540175771, prime_oneHundredThirtySevenEE_162405429905083]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539235 : Nat.totient 161970563122086672569056539235 = 129038788846121180174459481600 := by
  rw [← show ((([(5, 1), (241, 1), (4132431547, 1), (32526952606910261, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_241, prime_oneHundredThirtySevenEE_4132431547, prime_oneHundredThirtySevenEE_32526952606910261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539236 : Nat.totient 161970563122086672569056539236 = 76221289169800369953262797440 := by
  rw [← show ((([(2, 2), (17, 1), (500471, 1), (4759356777741446162687, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_500471, prime_oneHundredThirtySevenEE_4759356777741446162687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539237 : Nat.totient 161970563122086672569056539237 = 107979987200534387422716933360 := by
  rw [← show ((([(3, 1), (278147, 1), (139483091347, 1), (1391614333231, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_278147, prime_oneHundredThirtySevenEE_139483091347, prime_oneHundredThirtySevenEE_1391614333231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539238 : Nat.totient 161970563122086672569056539238 = 69415955623751431101024231096 := by
  rw [← show ((([(2, 1), (7, 1), (11569325937291905183504038517, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_11569325937291905183504038517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539239 : Nat.totient 161970563122086672569056539239 = 161958295911171906100212382656 := by
  rw [← show ((([(14293, 1), (173209, 1), (65424775946616105347, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_14293, prime_oneHundredThirtySevenEE_173209, prime_oneHundredThirtySevenEE_65424775946616105347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539240 : Nat.totient 161970563122086672569056539240 = 43192150165878302386863206784 := by
  rw [← show ((([(2, 3), (3, 2), (5, 1), (3889947657703, 1), (115661769896503, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_3889947657703, prime_oneHundredThirtySevenEE_115661769896503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539241 : Nat.totient 161970563122086672569056539241 = 135845764280803984184645649600 := by
  rw [← show ((([(11, 1), (13, 2), (1847, 1), (1019494547, 1), (46270575343511, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_1847, prime_oneHundredThirtySevenEE_1019494547, prime_oneHundredThirtySevenEE_46270575343511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539242 : Nat.totient 161970563122086672569056539242 = 80150069238681044096306547840 := by
  rw [← show ((([(2, 1), (97, 1), (256471, 1), (3255338069051328456883, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_97, prime_oneHundredThirtySevenEE_256471, prime_oneHundredThirtySevenEE_3255338069051328456883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539243 : Nat.totient 161970563122086672569056539243 = 104256665942609283289219313280 := by
  rw [← show ((([(3, 1), (29, 1), (423853, 1), (45793103, 1), (95918307115471, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_29, prime_oneHundredThirtySevenEE_423853, prime_oneHundredThirtySevenEE_45793103, prime_oneHundredThirtySevenEE_95918307115471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539244 : Nat.totient 161970563122086672569056539244 = 80955482526491780033282748240 := by
  rw [← show ((([(2, 2), (2719, 1), (5748199, 1), (2590807218358065331, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_2719, prime_oneHundredThirtySevenEE_5748199, prime_oneHundredThirtySevenEE_2590807218358065331]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539245 : Nat.totient 161970563122086672569056539245 = 107448331430300610036993638400 := by
  rw [← show ((([(5, 1), (7, 1), (31, 1), (3121, 1), (47831344119613875550657, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_31, prime_oneHundredThirtySevenEE_3121, prime_oneHundredThirtySevenEE_47831344119613875550657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539246 : Nat.totient 161970563122086672569056539246 = 53127892122055613999607350880 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1), (523, 1), (573379, 1), (1267894217814040763, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_71, prime_oneHundredThirtySevenEE_523, prime_oneHundredThirtySevenEE_573379, prime_oneHundredThirtySevenEE_1267894217814040763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539247 : Nat.totient 161970563122086672569056539247 = 161325262073791506542884999000 := by
  rw [← show ((([(251, 1), (645301048295166026171539997, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_251, prime_oneHundredThirtySevenEE_645301048295166026171539997]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539248 : Nat.totient 161970563122086672569056539248 = 80985280219727007205351892160 := by
  rw [← show ((([(2, 4), (73245391, 1), (343968199, 1), (401807015567, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_73245391, prime_oneHundredThirtySevenEE_343968199, prime_oneHundredThirtySevenEE_401807015567]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539249 : Nat.totient 161970563122086672569056539249 = 103285576471623393055575060672 := by
  rw [← show ((([(3, 2), (23, 1), (8588467079, 1), (91106652830484233, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_23, prime_oneHundredThirtySevenEE_8588467079, prime_oneHundredThirtySevenEE_91106652830484233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539250 : Nat.totient 161970563122086672569056539250 = 64764815044892203602542688000 := by
  rw [← show ((([(2, 1), (5, 3), (2903, 1), (59281, 1), (3764727327801072299, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_2903, prime_oneHundredThirtySevenEE_59281, prime_oneHundredThirtySevenEE_3764727327801072299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539251 : Nat.totient 161970563122086672569056539251 = 153445796299369850134414432968 := by
  rw [← show ((([(19, 1), (447877007, 1), (19033722086362484047, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_19, prime_oneHundredThirtySevenEE_447877007, prime_oneHundredThirtySevenEE_19033722086362484047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539252 : Nat.totient 161970563122086672569056539252 = 42069928903218939547186790400 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11, 1), (121171, 1), (1209325529, 1), (1196250708097, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_121171, prime_oneHundredThirtySevenEE_1209325529, prime_oneHundredThirtySevenEE_1196250708097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539253 : Nat.totient 161970563122086672569056539253 = 152392080919010141568156327936 := by
  rw [← show ((([(17, 1), (4259, 1), (12269, 1), (58913, 1), (3094989824463283, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_4259, prime_oneHundredThirtySevenEE_12269, prime_oneHundredThirtySevenEE_58913, prime_oneHundredThirtySevenEE_3094989824463283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539254 : Nat.totient 161970563122086672569056539254 = 74184989772074584065933198240 := by
  rw [← show ((([(2, 1), (13, 1), (131, 1), (76411163, 1), (622349920854818743, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_131, prime_oneHundredThirtySevenEE_76411163, prime_oneHundredThirtySevenEE_622349920854818743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539255 : Nat.totient 161970563122086672569056539255 = 85591836891837228190725144576 := by
  rw [← show ((([(3, 1), (5, 1), (173, 1), (293, 1), (9045217, 1), (23551150039774009, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_173, prime_oneHundredThirtySevenEE_293, prime_oneHundredThirtySevenEE_9045217, prime_oneHundredThirtySevenEE_23551150039774009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539256 : Nat.totient 161970563122086672569056539256 = 79629635118627183104621568000 := by
  rw [← show ((([(2, 3), (61, 1), (2843, 1), (22685403409, 1), (5146273981201, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_61, prime_oneHundredThirtySevenEE_2843, prime_oneHundredThirtySevenEE_22685403409, prime_oneHundredThirtySevenEE_5146273981201]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539257 : Nat.totient 161970563122086672569056539257 = 161940771082598193201946067712 := by
  rw [← show ((([(5437, 1), (100561277, 1), (296241555478489393, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5437, prime_oneHundredThirtySevenEE_100561277, prime_oneHundredThirtySevenEE_296241555478489393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539258 : Nat.totient 161970563122086672569056539258 = 52530993445001082995369686464 := by
  rw [← show ((([(2, 1), (3, 4), (37, 1), (27022115969650762857700457, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_37, prime_oneHundredThirtySevenEE_27022115969650762857700457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539259 : Nat.totient 161970563122086672569056539259 = 138759338371520736244479633408 := by
  rw [← show ((([(7, 1), (1913, 1), (536771808673, 1), (22533745421813, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_1913, prime_oneHundredThirtySevenEE_536771808673, prime_oneHundredThirtySevenEE_22533745421813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539260 : Nat.totient 161970563122086672569056539260 = 64788129525653113812534768704 := by
  rw [← show ((([(2, 2), (5, 1), (676829, 1), (11965397694401885304047, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_676829, prime_oneHundredThirtySevenEE_11965397694401885304047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539261 : Nat.totient 161970563122086672569056539261 = 107980194517924031027462650320 := by
  rw [← show ((([(3, 1), (596917, 1), (90448400208675953591011, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_596917, prime_oneHundredThirtySevenEE_90448400208675953591011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539262 : Nat.totient 161970563122086672569056539262 = 80985281561043336284528269630 := by
  rw [← show ((([(2, 1), (80985281561043336284528269631, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_80985281561043336284528269631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539263 : Nat.totient 161970563122086672569056539263 = 143654601438657802722001364800 := by
  rw [← show ((([(11, 1), (41, 1), (359136503596644506805003413, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_41, prime_oneHundredThirtySevenEE_359136503596644506805003413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539264 : Nat.totient 161970563122086672569056539264 = 53968720962569530701974835200 := by
  rw [← show ((([(2, 7), (3, 1), (2591, 1), (86531, 1), (9888023, 1), (190263842837, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_2591, prime_oneHundredThirtySevenEE_86531, prime_oneHundredThirtySevenEE_9888023, prime_oneHundredThirtySevenEE_190263842837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539265 : Nat.totient 161970563122086672569056539265 = 129576450497669338055245231408 := by
  rw [← show ((([(5, 1), (32394112624417334513811307853, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_32394112624417334513811307853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539266 : Nat.totient 161970563122086672569056539266 = 67801631073706136246834194560 := by
  rw [← show ((([(2, 1), (7, 1), (43, 1), (103403333513, 1), (2601986632578941, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_43, prime_oneHundredThirtySevenEE_103403333513, prime_oneHundredThirtySevenEE_2601986632578941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539267 : Nat.totient 161970563122086672569056539267 = 99674192689800150819119788800 := by
  rw [← show ((([(3, 2), (13, 1), (139460138791, 1), (9926591206415761, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_139460138791, prime_oneHundredThirtySevenEE_9926591206415761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539268 : Nat.totient 161970563122086672569056539268 = 80242297318146651001866715680 := by
  rw [← show ((([(2, 2), (109, 1), (9562104443, 1), (38850455929128191, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_109, prime_oneHundredThirtySevenEE_9562104443, prime_oneHundredThirtySevenEE_38850455929128191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539269 : Nat.totient 161970563122086672569056539269 = 161837033479317722023656234480 := by
  rw [← show ((([(1213, 1), (219693203, 1), (607797165753850771, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_1213, prime_oneHundredThirtySevenEE_219693203, prime_oneHundredThirtySevenEE_607797165753850771]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539270 : Nat.totient 161970563122086672569056539270 = 37547389708225417555476480000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (17, 1), (19, 1), (59, 1), (151, 1), (641, 1), (16369, 1), (583783, 1), (306303341, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_19, prime_oneHundredThirtySevenEE_59, prime_oneHundredThirtySevenEE_151, prime_oneHundredThirtySevenEE_641, prime_oneHundredThirtySevenEE_16369, prime_oneHundredThirtySevenEE_583783, prime_oneHundredThirtySevenEE_306303341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539271 : Nat.totient 161970563122086672569056539271 = 161970563108081413090590828544 := by
  rw [← show ((([(11564981249, 1), (14005259466900729479, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_11564981249, prime_oneHundredThirtySevenEE_14005259466900729479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539272 : Nat.totient 161970563122086672569056539272 = 73711740627648948095170099200 := by
  rw [← show ((([(2, 3), (23, 1), (29, 1), (73, 1), (1301, 1), (319609819987516598399, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_23, prime_oneHundredThirtySevenEE_29, prime_oneHundredThirtySevenEE_73, prime_oneHundredThirtySevenEE_1301, prime_oneHundredThirtySevenEE_319609819987516598399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539273 : Nat.totient 161970563122086672569056539273 = 91947856615219448265566146464 := by
  rw [← show ((([(3, 1), (7, 2), (227, 1), (463, 1), (10483635412188008888959, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_227, prime_oneHundredThirtySevenEE_463, prime_oneHundredThirtySevenEE_10483635412188008888959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539274 : Nat.totient 161970563122086672569056539274 = 73622983237312123895025699660 := by
  rw [← show ((([(2, 1), (11, 1), (7362298323731212389502569967, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_7362298323731212389502569967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539275 : Nat.totient 161970563122086672569056539275 = 125326632249706406955013939200 := by
  rw [← show ((([(5, 2), (47, 1), (149, 1), (197, 1), (55127, 1), (4463761, 1), (19084484723, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_47, prime_oneHundredThirtySevenEE_149, prime_oneHundredThirtySevenEE_197, prime_oneHundredThirtySevenEE_55127, prime_oneHundredThirtySevenEE_4463761, prime_oneHundredThirtySevenEE_19084484723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539276 : Nat.totient 161970563122086672569056539276 = 52248568749060216957760173600 := by
  rw [← show ((([(2, 2), (3, 2), (31, 1), (145134913191833935993778261, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_31, prime_oneHundredThirtySevenEE_145134913191833935993778261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539277 : Nat.totient 161970563122086672569056539277 = 160396697064223704279214609920 := by
  rw [← show ((([(103, 1), (120067, 1), (387047761, 1), (33838464559657, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_103, prime_oneHundredThirtySevenEE_120067, prime_oneHundredThirtySevenEE_387047761, prime_oneHundredThirtySevenEE_33838464559657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539278 : Nat.totient 161970563122086672569056539278 = 80985281560744714642490037160 := by
  rw [← show ((([(2, 1), (271197206459, 1), (298621370841026021, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_271197206459, prime_oneHundredThirtySevenEE_298621370841026021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539279 : Nat.totient 161970563122086672569056539279 = 106715730540809912128655071232 := by
  rw [← show ((([(3, 1), (107, 1), (419, 1), (588737, 1), (2045482207736893733, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_107, prime_oneHundredThirtySevenEE_419, prime_oneHundredThirtySevenEE_588737, prime_oneHundredThirtySevenEE_2045482207736893733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539280 : Nat.totient 161970563122086672569056539280 = 50610451693854122075441479680 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (13, 1), (79, 1), (38711, 1), (132953, 1), (54719874138143, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_79, prime_oneHundredThirtySevenEE_38711, prime_oneHundredThirtySevenEE_132953, prime_oneHundredThirtySevenEE_54719874138143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539281 : Nat.totient 161970563122086672569056539281 = 161778264324324130740902131600 := by
  rw [← show ((([(863, 1), (35051, 1), (5354573490450305686637, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_863, prime_oneHundredThirtySevenEE_35051, prime_oneHundredThirtySevenEE_5354573490450305686637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539282 : Nat.totient 161970563122086672569056539282 = 53182549525436137625460483600 := by
  rw [← show ((([(2, 1), (3, 1), (67, 1), (29311, 1), (13746096979373090584831, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_67, prime_oneHundredThirtySevenEE_29311, prime_oneHundredThirtySevenEE_13746096979373090584831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539283 : Nat.totient 161970563122086672569056539283 = 161970539574421953674346395880 := by
  rw [← show ((([(6878413, 1), (23547664718894703264991, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_6878413, prime_oneHundredThirtySevenEE_23547664718894703264991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539284 : Nat.totient 161970563122086672569056539284 = 80913640922934662157285784320 := by
  rw [← show ((([(2, 2), (1987, 1), (2621, 1), (20837992969, 1), (373125839467, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_1987, prime_oneHundredThirtySevenEE_2621, prime_oneHundredThirtySevenEE_20837992969, prime_oneHundredThirtySevenEE_373125839467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539285 : Nat.totient 161970563122086672569056539285 = 78531182117044577917211854080 := by
  rw [← show ((([(3, 3), (5, 1), (11, 1), (28504962349, 1), (3826389417466669, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_28504962349, prime_oneHundredThirtySevenEE_3826389417466669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539286 : Nat.totient 161970563122086672569056539286 = 79213559407412931628675891200 := by
  rw [← show ((([(2, 1), (53, 1), (353, 1), (4357, 1), (210401, 1), (1758553, 1), (2685126187, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_53, prime_oneHundredThirtySevenEE_353, prime_oneHundredThirtySevenEE_4357, prime_oneHundredThirtySevenEE_210401, prime_oneHundredThirtySevenEE_1758553, prime_oneHundredThirtySevenEE_2685126187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539287 : Nat.totient 161970563122086672569056539287 = 130665328232943870307810317312 := by
  rw [← show ((([(7, 1), (17, 1), (1361097169093165315706357473, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_17, prime_oneHundredThirtySevenEE_1361097169093165315706357473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539288 : Nat.totient 161970563122086672569056539288 = 53879324897128397203234215936 := by
  rw [← show ((([(2, 3), (3, 1), (487, 1), (29937916097, 1), (462886294735783, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_487, prime_oneHundredThirtySevenEE_29937916097, prime_oneHundredThirtySevenEE_462886294735783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539289 : Nat.totient 161970563122086672569056539289 = 150748398603623710551862707264 := by
  rw [← show ((([(19, 1), (83, 1), (179, 1), (86509, 1), (6632695747601761687, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_19, prime_oneHundredThirtySevenEE_83, prime_oneHundredThirtySevenEE_179, prime_oneHundredThirtySevenEE_86509, prime_oneHundredThirtySevenEE_6632695747601761687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539290 : Nat.totient 161970563122086672569056539290 = 64788225248833479926959493904 := by
  rw [← show ((([(2, 1), (5, 1), (71851680959987, 1), (225423484820467, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_71851680959987, prime_oneHundredThirtySevenEE_225423484820467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539291 : Nat.totient 161970563122086672569056539291 = 107278232118793796758059648000 := by
  rw [← show ((([(3, 1), (157, 1), (7481, 1), (4119307, 1), (75370901, 1), (148056563, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_157, prime_oneHundredThirtySevenEE_7481, prime_oneHundredThirtySevenEE_4119307, prime_oneHundredThirtySevenEE_75370901, prime_oneHundredThirtySevenEE_148056563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539292 : Nat.totient 161970563122086672569056539292 = 80519619262832066253186742464 := by
  rw [← show ((([(2, 2), (239, 1), (659, 1), (18979, 1), (419443, 1), (32295834323659, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_239, prime_oneHundredThirtySevenEE_659, prime_oneHundredThirtySevenEE_18979, prime_oneHundredThirtySevenEE_419443, prime_oneHundredThirtySevenEE_32295834323659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539293 : Nat.totient 161970563122086672569056539293 = 149511274971323901661438329600 := by
  rw [← show ((([(13, 1), (10630441, 1), (1172037367623258473321, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_13, prime_oneHundredThirtySevenEE_10630441, prime_oneHundredThirtySevenEE_1172037367623258473321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539294 : Nat.totient 161970563122086672569056539294 = 46277303748722092142300897280 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1), (103871430529, 1), (12375690342882161, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_103871430529, prime_oneHundredThirtySevenEE_12375690342882161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539295 : Nat.totient 161970563122086672569056539295 = 119237913015560836360373790720 := by
  rw [← show ((([(5, 1), (23, 1), (37, 1), (89, 1), (427707160438048225007081, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_23, prime_oneHundredThirtySevenEE_37, prime_oneHundredThirtySevenEE_89, prime_oneHundredThirtySevenEE_427707160438048225007081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539296 : Nat.totient 161970563122086672569056539296 = 73497372134609651490662400000 := by
  rw [← show ((([(2, 5), (11, 1), (881, 1), (1951, 1), (34819, 1), (58199, 1), (78803, 1), (1676431, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_11, prime_oneHundredThirtySevenEE_881, prime_oneHundredThirtySevenEE_1951, prime_oneHundredThirtySevenEE_34819, prime_oneHundredThirtySevenEE_58199, prime_oneHundredThirtySevenEE_78803, prime_oneHundredThirtySevenEE_1676431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539297 : Nat.totient 161970563122086672569056539297 = 107980375286629332380226911472 := by
  rw [← show ((([(3, 1), (842970277, 1), (64047557998729087087, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_842970277, prime_oneHundredThirtySevenEE_64047557998729087087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539298 : Nat.totient 161970563122086672569056539298 = 80985143539001100437268012000 := by
  rw [← show ((([(2, 1), (595801, 1), (38650631, 1), (3516804934767679, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_595801, prime_oneHundredThirtySevenEE_38650631, prime_oneHundredThirtySevenEE_3516804934767679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539299 : Nat.totient 161970563122086672569056539299 = 161970561275663946310193309640 := by
  rw [← show ((([(87721279, 1), (1846422726258775508381, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_87721279, prime_oneHundredThirtySevenEE_1846422726258775508381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539300 : Nat.totient 161970563122086672569056539300 = 43188273282974878836268208640 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (12637, 1), (94099, 1), (454031352754534637, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_2, prime_oneHundredThirtySevenEE_3, prime_oneHundredThirtySevenEE_5, prime_oneHundredThirtySevenEE_12637, prime_oneHundredThirtySevenEE_94099, prime_oneHundredThirtySevenEE_454031352754534637]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtySevenEE_161970563122086672569056539301 : Nat.totient 161970563122086672569056539301 = 134037043936209066133919886336 := by
  rw [← show ((([(7, 1), (29, 1), (17737, 1), (49952927, 1), (900531579922633, 1)] : List FactorBlock).map factorBlockValue).prod) = 161970563122086672569056539301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtySevenEE_7, prime_oneHundredThirtySevenEE_29, prime_oneHundredThirtySevenEE_17737, prime_oneHundredThirtySevenEE_49952927, prime_oneHundredThirtySevenEE_900531579922633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtySevenEE : certifiedKill 1 161970563122086672569056539199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtySevenEE_161970563122086672569056539200, phi_oneHundredThirtySevenEE_161970563122086672569056539201, phi_oneHundredThirtySevenEE_161970563122086672569056539202,
    phi_oneHundredThirtySevenEE_161970563122086672569056539203, phi_oneHundredThirtySevenEE_161970563122086672569056539204, phi_oneHundredThirtySevenEE_161970563122086672569056539205,
    phi_oneHundredThirtySevenEE_161970563122086672569056539206, phi_oneHundredThirtySevenEE_161970563122086672569056539207, phi_oneHundredThirtySevenEE_161970563122086672569056539208,
    phi_oneHundredThirtySevenEE_161970563122086672569056539209, phi_oneHundredThirtySevenEE_161970563122086672569056539210, phi_oneHundredThirtySevenEE_161970563122086672569056539211,
    phi_oneHundredThirtySevenEE_161970563122086672569056539212, phi_oneHundredThirtySevenEE_161970563122086672569056539213, phi_oneHundredThirtySevenEE_161970563122086672569056539214,
    phi_oneHundredThirtySevenEE_161970563122086672569056539215, phi_oneHundredThirtySevenEE_161970563122086672569056539216, phi_oneHundredThirtySevenEE_161970563122086672569056539217,
    phi_oneHundredThirtySevenEE_161970563122086672569056539218, phi_oneHundredThirtySevenEE_161970563122086672569056539219, phi_oneHundredThirtySevenEE_161970563122086672569056539220,
    phi_oneHundredThirtySevenEE_161970563122086672569056539221, phi_oneHundredThirtySevenEE_161970563122086672569056539222, phi_oneHundredThirtySevenEE_161970563122086672569056539223,
    phi_oneHundredThirtySevenEE_161970563122086672569056539224, phi_oneHundredThirtySevenEE_161970563122086672569056539225, phi_oneHundredThirtySevenEE_161970563122086672569056539226,
    phi_oneHundredThirtySevenEE_161970563122086672569056539227, phi_oneHundredThirtySevenEE_161970563122086672569056539228, phi_oneHundredThirtySevenEE_161970563122086672569056539229,
    phi_oneHundredThirtySevenEE_161970563122086672569056539230, phi_oneHundredThirtySevenEE_161970563122086672569056539231, phi_oneHundredThirtySevenEE_161970563122086672569056539232,
    phi_oneHundredThirtySevenEE_161970563122086672569056539233, phi_oneHundredThirtySevenEE_161970563122086672569056539234, phi_oneHundredThirtySevenEE_161970563122086672569056539235,
    phi_oneHundredThirtySevenEE_161970563122086672569056539236, phi_oneHundredThirtySevenEE_161970563122086672569056539237, phi_oneHundredThirtySevenEE_161970563122086672569056539238,
    phi_oneHundredThirtySevenEE_161970563122086672569056539239, phi_oneHundredThirtySevenEE_161970563122086672569056539240, phi_oneHundredThirtySevenEE_161970563122086672569056539241,
    phi_oneHundredThirtySevenEE_161970563122086672569056539242, phi_oneHundredThirtySevenEE_161970563122086672569056539243, phi_oneHundredThirtySevenEE_161970563122086672569056539244,
    phi_oneHundredThirtySevenEE_161970563122086672569056539245, phi_oneHundredThirtySevenEE_161970563122086672569056539246, phi_oneHundredThirtySevenEE_161970563122086672569056539247,
    phi_oneHundredThirtySevenEE_161970563122086672569056539248, phi_oneHundredThirtySevenEE_161970563122086672569056539249, phi_oneHundredThirtySevenEE_161970563122086672569056539250,
    phi_oneHundredThirtySevenEE_161970563122086672569056539251, phi_oneHundredThirtySevenEE_161970563122086672569056539252, phi_oneHundredThirtySevenEE_161970563122086672569056539253,
    phi_oneHundredThirtySevenEE_161970563122086672569056539254, phi_oneHundredThirtySevenEE_161970563122086672569056539255, phi_oneHundredThirtySevenEE_161970563122086672569056539256,
    phi_oneHundredThirtySevenEE_161970563122086672569056539257, phi_oneHundredThirtySevenEE_161970563122086672569056539258, phi_oneHundredThirtySevenEE_161970563122086672569056539259,
    phi_oneHundredThirtySevenEE_161970563122086672569056539260, phi_oneHundredThirtySevenEE_161970563122086672569056539261, phi_oneHundredThirtySevenEE_161970563122086672569056539262,
    phi_oneHundredThirtySevenEE_161970563122086672569056539263, phi_oneHundredThirtySevenEE_161970563122086672569056539264, phi_oneHundredThirtySevenEE_161970563122086672569056539265,
    phi_oneHundredThirtySevenEE_161970563122086672569056539266, phi_oneHundredThirtySevenEE_161970563122086672569056539267, phi_oneHundredThirtySevenEE_161970563122086672569056539268,
    phi_oneHundredThirtySevenEE_161970563122086672569056539269, phi_oneHundredThirtySevenEE_161970563122086672569056539270, phi_oneHundredThirtySevenEE_161970563122086672569056539271,
    phi_oneHundredThirtySevenEE_161970563122086672569056539272, phi_oneHundredThirtySevenEE_161970563122086672569056539273, phi_oneHundredThirtySevenEE_161970563122086672569056539274,
    phi_oneHundredThirtySevenEE_161970563122086672569056539275, phi_oneHundredThirtySevenEE_161970563122086672569056539276, phi_oneHundredThirtySevenEE_161970563122086672569056539277,
    phi_oneHundredThirtySevenEE_161970563122086672569056539278, phi_oneHundredThirtySevenEE_161970563122086672569056539279, phi_oneHundredThirtySevenEE_161970563122086672569056539280,
    phi_oneHundredThirtySevenEE_161970563122086672569056539281, phi_oneHundredThirtySevenEE_161970563122086672569056539282, phi_oneHundredThirtySevenEE_161970563122086672569056539283,
    phi_oneHundredThirtySevenEE_161970563122086672569056539284, phi_oneHundredThirtySevenEE_161970563122086672569056539285, phi_oneHundredThirtySevenEE_161970563122086672569056539286,
    phi_oneHundredThirtySevenEE_161970563122086672569056539287, phi_oneHundredThirtySevenEE_161970563122086672569056539288, phi_oneHundredThirtySevenEE_161970563122086672569056539289,
    phi_oneHundredThirtySevenEE_161970563122086672569056539290, phi_oneHundredThirtySevenEE_161970563122086672569056539291, phi_oneHundredThirtySevenEE_161970563122086672569056539292,
    phi_oneHundredThirtySevenEE_161970563122086672569056539293, phi_oneHundredThirtySevenEE_161970563122086672569056539294, phi_oneHundredThirtySevenEE_161970563122086672569056539295,
    phi_oneHundredThirtySevenEE_161970563122086672569056539296, phi_oneHundredThirtySevenEE_161970563122086672569056539297, phi_oneHundredThirtySevenEE_161970563122086672569056539298,
    phi_oneHundredThirtySevenEE_161970563122086672569056539299, phi_oneHundredThirtySevenEE_161970563122086672569056539300, phi_oneHundredThirtySevenEE_161970563122086672569056539301]

end TotientTailPeriodKiller
end Erdos249257
