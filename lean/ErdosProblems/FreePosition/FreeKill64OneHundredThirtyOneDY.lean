import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyOneDYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyOneDYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyOneDYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyOneDYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyOneDYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyOneDYFastPow a n * oneHundredThirtyOneDYFastPow a n * a else oneHundredThirtyOneDYFastPow a n * oneHundredThirtyOneDYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyOneDY_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyOneDY_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyOneDY_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyOneDY_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyOneDY_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyOneDY_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyOneDY_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyOneDY_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyOneDY_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyOneDY_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyOneDY_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyOneDY_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyOneDY_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyOneDY_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyOneDY_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyOneDY_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyOneDY_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyOneDY_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyOneDY_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyOneDY_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyOneDY_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyOneDY_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyOneDY_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyOneDY_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyOneDY_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyOneDY_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyOneDY_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyOneDY_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyOneDY_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyOneDY_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyOneDY_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyOneDY_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyOneDY_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyOneDY_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyOneDY_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyOneDY_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyOneDY_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyOneDY_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyOneDY_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyOneDY_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyOneDY_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyOneDY_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyOneDY_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyOneDY_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyOneDY_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyOneDY_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyOneDY_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirtyOneDY_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyOneDY_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyOneDY_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyOneDY_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyOneDY_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredThirtyOneDY_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThirtyOneDY_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtyOneDY_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtyOneDY_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredThirtyOneDY_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtyOneDY_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtyOneDY_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirtyOneDY_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredThirtyOneDY_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredThirtyOneDY_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtyOneDY_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyOneDY_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredThirtyOneDY_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtyOneDY_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtyOneDY_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtyOneDY_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyOneDY_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyOneDY_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirtyOneDY_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirtyOneDY_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredThirtyOneDY_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtyOneDY_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtyOneDY_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredThirtyOneDY_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirtyOneDY_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredThirtyOneDY_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredThirtyOneDY_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyOneDY_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredThirtyOneDY_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredThirtyOneDY_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyOneDY_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredThirtyOneDY_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThirtyOneDY_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredThirtyOneDY_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThirtyOneDY_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredThirtyOneDY_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredThirtyOneDY_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredThirtyOneDY_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredThirtyOneDY_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredThirtyOneDY_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredThirtyOneDY_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredThirtyOneDY_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredThirtyOneDY_857 : Nat.Prime 857 := by norm_num

private theorem prime_oneHundredThirtyOneDY_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirtyOneDY_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThirtyOneDY_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredThirtyOneDY_937 : Nat.Prime 937 := by norm_num

private theorem prime_oneHundredThirtyOneDY_941 : Nat.Prime 941 := by norm_num

private theorem prime_oneHundredThirtyOneDY_977 : Nat.Prime 977 := by norm_num

private theorem prime_oneHundredThirtyOneDY_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1021 : Nat.Prime 1021 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1039 : Nat.Prime 1039 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1213 : Nat.Prime 1213 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1223 : Nat.Prime 1223 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1291 : Nat.Prime 1291 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1307 : Nat.Prime 1307 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1543 : Nat.Prime 1543 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1879 : Nat.Prime 1879 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1889 : Nat.Prime 1889 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1907 : Nat.Prime 1907 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2393 : Nat.Prime 2393 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3191 : Nat.Prime 3191 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3259 : Nat.Prime 3259 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3539 : Nat.Prime 3539 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3583 : Nat.Prime 3583 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3593 : Nat.Prime 3593 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3643 : Nat.Prime 3643 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4007 : Nat.Prime 4007 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4027 : Nat.Prime 4027 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4139 : Nat.Prime 4139 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4289 : Nat.Prime 4289 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4297 : Nat.Prime 4297 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4649 : Nat.Prime 4649 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4877 : Nat.Prime 4877 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4993 : Nat.Prime 4993 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5101 : Nat.Prime 5101 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5147 : Nat.Prime 5147 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5501 : Nat.Prime 5501 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5623 : Nat.Prime 5623 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5791 : Nat.Prime 5791 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5851 : Nat.Prime 5851 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5857 : Nat.Prime 5857 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6229 : Nat.Prime 6229 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6661 : Nat.Prime 6661 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6899 : Nat.Prime 6899 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7043 : Nat.Prime 7043 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7069 : Nat.Prime 7069 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7121 : Nat.Prime 7121 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7459 : Nat.Prime 7459 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7829 : Nat.Prime 7829 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7937 : Nat.Prime 7937 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8221 : Nat.Prime 8221 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8461 : Nat.Prime 8461 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8719 : Nat.Prime 8719 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8753 : Nat.Prime 8753 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8867 : Nat.Prime 8867 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8999 : Nat.Prime 8999 := by norm_num

private theorem prime_oneHundredThirtyOneDY_9049 : Nat.Prime 9049 := by norm_num

private theorem prime_oneHundredThirtyOneDY_9059 : Nat.Prime 9059 := by norm_num

private theorem prime_oneHundredThirtyOneDY_9161 : Nat.Prime 9161 := by norm_num

private theorem prime_oneHundredThirtyOneDY_9791 : Nat.Prime 9791 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10303 : Nat.Prime 10303 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10433 : Nat.Prime 10433 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10733 : Nat.Prime 10733 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11057 : Nat.Prime 11057 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11087 : Nat.Prime 11087 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11261 : Nat.Prime 11261 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11329 : Nat.Prime 11329 := by norm_num

private theorem prime_oneHundredThirtyOneDY_11657 : Nat.Prime 11657 := by norm_num

private theorem prime_oneHundredThirtyOneDY_12049 : Nat.Prime 12049 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13009 : Nat.Prime 13009 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13033 : Nat.Prime 13033 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13241 : Nat.Prime 13241 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13339 : Nat.Prime 13339 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13577 : Nat.Prime 13577 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13759 : Nat.Prime 13759 := by norm_num

private theorem prime_oneHundredThirtyOneDY_14207 : Nat.Prime 14207 := by norm_num

private theorem prime_oneHundredThirtyOneDY_14503 : Nat.Prime 14503 := by norm_num

private theorem prime_oneHundredThirtyOneDY_14951 : Nat.Prime 14951 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15307 : Nat.Prime 15307 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15377 : Nat.Prime 15377 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15569 : Nat.Prime 15569 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15581 : Nat.Prime 15581 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15749 : Nat.Prime 15749 := by norm_num

private theorem prime_oneHundredThirtyOneDY_15913 : Nat.Prime 15913 := by norm_num

private theorem prime_oneHundredThirtyOneDY_16073 : Nat.Prime 16073 := by norm_num

private theorem prime_oneHundredThirtyOneDY_16363 : Nat.Prime 16363 := by norm_num

private theorem prime_oneHundredThirtyOneDY_16433 : Nat.Prime 16433 := by norm_num

private theorem prime_oneHundredThirtyOneDY_16871 : Nat.Prime 16871 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17107 : Nat.Prime 17107 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17417 : Nat.Prime 17417 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17929 : Nat.Prime 17929 := by norm_num

private theorem prime_oneHundredThirtyOneDY_18353 : Nat.Prime 18353 := by norm_num

private theorem prime_oneHundredThirtyOneDY_18617 : Nat.Prime 18617 := by norm_num

private theorem prime_oneHundredThirtyOneDY_19463 : Nat.Prime 19463 := by norm_num

private theorem prime_oneHundredThirtyOneDY_19867 : Nat.Prime 19867 := by norm_num

private theorem prime_oneHundredThirtyOneDY_20021 : Nat.Prime 20021 := by norm_num

private theorem prime_oneHundredThirtyOneDY_20389 : Nat.Prime 20389 := by norm_num

private theorem prime_oneHundredThirtyOneDY_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21017 : Nat.Prime 21017 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21149 : Nat.Prime 21149 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21191 : Nat.Prime 21191 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21377 : Nat.Prime 21377 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21419 : Nat.Prime 21419 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21589 : Nat.Prime 21589 := by norm_num

private theorem prime_oneHundredThirtyOneDY_22051 : Nat.Prime 22051 := by norm_num

private theorem prime_oneHundredThirtyOneDY_22409 : Nat.Prime 22409 := by norm_num

private theorem prime_oneHundredThirtyOneDY_22433 : Nat.Prime 22433 := by norm_num

private theorem prime_oneHundredThirtyOneDY_22619 : Nat.Prime 22619 := by norm_num

private theorem prime_oneHundredThirtyOneDY_22961 : Nat.Prime 22961 := by norm_num

private theorem prime_oneHundredThirtyOneDY_25031 : Nat.Prime 25031 := by norm_num

private theorem prime_oneHundredThirtyOneDY_25321 : Nat.Prime 25321 := by norm_num

private theorem prime_oneHundredThirtyOneDY_25741 : Nat.Prime 25741 := by norm_num

private theorem prime_oneHundredThirtyOneDY_26513 : Nat.Prime 26513 := by norm_num

private theorem prime_oneHundredThirtyOneDY_26927 : Nat.Prime 26927 := by norm_num

private theorem prime_oneHundredThirtyOneDY_28229 : Nat.Prime 28229 := by norm_num

private theorem prime_oneHundredThirtyOneDY_29569 : Nat.Prime 29569 := by norm_num

private theorem prime_oneHundredThirtyOneDY_29959 : Nat.Prime 29959 := by norm_num

private theorem prime_oneHundredThirtyOneDY_30211 : Nat.Prime 30211 := by norm_num

private theorem prime_oneHundredThirtyOneDY_30493 : Nat.Prime 30493 := by norm_num

private theorem prime_oneHundredThirtyOneDY_32027 : Nat.Prime 32027 := by norm_num

private theorem prime_oneHundredThirtyOneDY_32843 : Nat.Prime 32843 := by norm_num

private theorem prime_oneHundredThirtyOneDY_33427 : Nat.Prime 33427 := by norm_num

private theorem prime_oneHundredThirtyOneDY_33811 : Nat.Prime 33811 := by norm_num

private theorem prime_oneHundredThirtyOneDY_37967 : Nat.Prime 37967 := by norm_num

private theorem prime_oneHundredThirtyOneDY_41131 : Nat.Prime 41131 := by norm_num

private theorem prime_oneHundredThirtyOneDY_41227 : Nat.Prime 41227 := by norm_num

private theorem prime_oneHundredThirtyOneDY_41413 : Nat.Prime 41413 := by norm_num

private theorem prime_oneHundredThirtyOneDY_45757 : Nat.Prime 45757 := by norm_num

private theorem prime_oneHundredThirtyOneDY_47591 : Nat.Prime 47591 := by norm_num

private theorem prime_oneHundredThirtyOneDY_50503 : Nat.Prime 50503 := by norm_num

private theorem prime_oneHundredThirtyOneDY_50929 : Nat.Prime 50929 := by norm_num

private theorem prime_oneHundredThirtyOneDY_53597 : Nat.Prime 53597 := by norm_num

private theorem prime_oneHundredThirtyOneDY_53777 : Nat.Prime 53777 := by norm_num

private theorem prime_oneHundredThirtyOneDY_54907 : Nat.Prime 54907 := by norm_num

private theorem prime_oneHundredThirtyOneDY_56041 : Nat.Prime 56041 := by norm_num

private theorem prime_oneHundredThirtyOneDY_58321 : Nat.Prime 58321 := by norm_num

private theorem prime_oneHundredThirtyOneDY_64319 : Nat.Prime 64319 := by norm_num

private theorem prime_oneHundredThirtyOneDY_64499 : Nat.Prime 64499 := by norm_num

private theorem prime_oneHundredThirtyOneDY_66863 : Nat.Prime 66863 := by norm_num

private theorem prime_oneHundredThirtyOneDY_67489 : Nat.Prime 67489 := by norm_num

private theorem prime_oneHundredThirtyOneDY_68147 : Nat.Prime 68147 := by norm_num

private theorem prime_oneHundredThirtyOneDY_69383 : Nat.Prime 69383 := by norm_num

private theorem prime_oneHundredThirtyOneDY_69761 : Nat.Prime 69761 := by norm_num

private theorem prime_oneHundredThirtyOneDY_72937 : Nat.Prime 72937 := by norm_num

private theorem prime_oneHundredThirtyOneDY_77773 : Nat.Prime 77773 := by norm_num

private theorem prime_oneHundredThirtyOneDY_78697 : Nat.Prime 78697 := by norm_num

private theorem prime_oneHundredThirtyOneDY_83459 : Nat.Prime 83459 := by norm_num

private theorem prime_oneHundredThirtyOneDY_84011 : Nat.Prime 84011 := by norm_num

private theorem prime_oneHundredThirtyOneDY_86561 : Nat.Prime 86561 := by norm_num

private theorem prime_oneHundredThirtyOneDY_88589 : Nat.Prime 88589 := by norm_num

private theorem prime_oneHundredThirtyOneDY_89477 : Nat.Prime 89477 := by norm_num

private theorem prime_oneHundredThirtyOneDY_92507 : Nat.Prime 92507 := by norm_num

private theorem prime_oneHundredThirtyOneDY_96443 : Nat.Prime 96443 := by norm_num

private theorem prime_oneHundredThirtyOneDY_102199 : Nat.Prime 102199 := by norm_num

private theorem prime_oneHundredThirtyOneDY_105607 : Nat.Prime 105607 := by norm_num

private theorem prime_oneHundredThirtyOneDY_106921 : Nat.Prime 106921 := by norm_num

private theorem prime_oneHundredThirtyOneDY_107719 : Nat.Prime 107719 := by norm_num

private theorem prime_oneHundredThirtyOneDY_108887 : Nat.Prime 108887 := by norm_num

private theorem prime_oneHundredThirtyOneDY_109961 : Nat.Prime 109961 := by norm_num

private theorem prime_oneHundredThirtyOneDY_117431 : Nat.Prime 117431 := by norm_num

private theorem prime_oneHundredThirtyOneDY_122033 : Nat.Prime 122033 := by norm_num

private theorem prime_oneHundredThirtyOneDY_124343 : Nat.Prime 124343 := by norm_num

private theorem prime_oneHundredThirtyOneDY_124601 : Nat.Prime 124601 := by norm_num

private theorem prime_oneHundredThirtyOneDY_125231 : Nat.Prime 125231 := by norm_num

private theorem prime_oneHundredThirtyOneDY_132157 : Nat.Prime 132157 := by norm_num

private theorem prime_oneHundredThirtyOneDY_134399 : Nat.Prime 134399 := by norm_num

private theorem prime_oneHundredThirtyOneDY_140269 : Nat.Prime 140269 := by norm_num

private theorem prime_oneHundredThirtyOneDY_143137 : Nat.Prime 143137 := by norm_num

private theorem prime_oneHundredThirtyOneDY_144497 : Nat.Prime 144497 := by norm_num

private theorem prime_oneHundredThirtyOneDY_156493 : Nat.Prime 156493 := by norm_num

private theorem prime_oneHundredThirtyOneDY_162691 : Nat.Prime 162691 := by norm_num

private theorem prime_oneHundredThirtyOneDY_166207 : Nat.Prime 166207 := by norm_num

private theorem prime_oneHundredThirtyOneDY_167879 : Nat.Prime 167879 := by norm_num

private theorem prime_oneHundredThirtyOneDY_168071 : Nat.Prime 168071 := by norm_num

private theorem prime_oneHundredThirtyOneDY_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyOneDY_176081 : Nat.Prime 176081 := by norm_num

private theorem prime_oneHundredThirtyOneDY_178037 : Nat.Prime 178037 := by norm_num

private theorem prime_oneHundredThirtyOneDY_178859 : Nat.Prime 178859 := by norm_num

private theorem prime_oneHundredThirtyOneDY_179287 : Nat.Prime 179287 := by norm_num

private theorem prime_oneHundredThirtyOneDY_185051 : Nat.Prime 185051 := by norm_num

private theorem prime_oneHundredThirtyOneDY_188323 : Nat.Prime 188323 := by norm_num

private theorem prime_oneHundredThirtyOneDY_197059 : Nat.Prime 197059 := by norm_num

private theorem prime_oneHundredThirtyOneDY_200117 : Nat.Prime 200117 := by norm_num

private theorem prime_oneHundredThirtyOneDY_203311 : Nat.Prime 203311 := by norm_num

private theorem prime_oneHundredThirtyOneDY_208367 : Nat.Prime 208367 := by norm_num

private theorem prime_oneHundredThirtyOneDY_218003 : Nat.Prime 218003 := by norm_num

private theorem prime_oneHundredThirtyOneDY_261631 : Nat.Prime 261631 := by norm_num

private theorem prime_oneHundredThirtyOneDY_272249 : Nat.Prime 272249 := by norm_num

private theorem prime_oneHundredThirtyOneDY_277247 : Nat.Prime 277247 := by norm_num

private theorem prime_oneHundredThirtyOneDY_282827 : Nat.Prime 282827 := by norm_num

private theorem prime_oneHundredThirtyOneDY_292133 : Nat.Prime 292133 := by norm_num

private theorem prime_oneHundredThirtyOneDY_296353 : Nat.Prime 296353 := by norm_num

private theorem prime_oneHundredThirtyOneDY_305597 : Nat.Prime 305597 := by norm_num

private theorem prime_oneHundredThirtyOneDY_312673 : Nat.Prime 312673 := by norm_num

private theorem prime_oneHundredThirtyOneDY_318077 : Nat.Prime 318077 := by norm_num

private theorem prime_oneHundredThirtyOneDY_321547 : Nat.Prime 321547 := by norm_num

private theorem prime_oneHundredThirtyOneDY_327799 : Nat.Prime 327799 := by norm_num

private theorem prime_oneHundredThirtyOneDY_344153 : Nat.Prime 344153 := by norm_num

private theorem prime_oneHundredThirtyOneDY_363269 : Nat.Prime 363269 := by norm_num

private theorem prime_oneHundredThirtyOneDY_366139 : Nat.Prime 366139 := by norm_num

private theorem prime_oneHundredThirtyOneDY_373157 : Nat.Prime 373157 := by norm_num

private theorem prime_oneHundredThirtyOneDY_373561 : Nat.Prime 373561 := by norm_num

private theorem prime_oneHundredThirtyOneDY_376853 : Nat.Prime 376853 := by norm_num

private theorem prime_oneHundredThirtyOneDY_415543 : Nat.Prime 415543 := by norm_num

private theorem prime_oneHundredThirtyOneDY_433361 : Nat.Prime 433361 := by norm_num

private theorem prime_oneHundredThirtyOneDY_435263 : Nat.Prime 435263 := by norm_num

private theorem prime_oneHundredThirtyOneDY_446569 : Nat.Prime 446569 := by norm_num

private theorem prime_oneHundredThirtyOneDY_457271 : Nat.Prime 457271 := by norm_num

private theorem prime_oneHundredThirtyOneDY_461191 : Nat.Prime 461191 := by norm_num

private theorem prime_oneHundredThirtyOneDY_489161 : Nat.Prime 489161 := by norm_num

private theorem prime_oneHundredThirtyOneDY_523169 : Nat.Prime 523169 := by norm_num

private theorem prime_oneHundredThirtyOneDY_547361 : Nat.Prime 547361 := by norm_num

private theorem prime_oneHundredThirtyOneDY_555257 : Nat.Prime 555257 := by norm_num

private theorem prime_oneHundredThirtyOneDY_577559 : Nat.Prime 577559 := by norm_num

private theorem prime_oneHundredThirtyOneDY_608297 : Nat.Prime 608297 := by norm_num

private theorem prime_oneHundredThirtyOneDY_609071 : Nat.Prime 609071 := by norm_num

private theorem prime_oneHundredThirtyOneDY_624089 : Nat.Prime 624089 := by norm_num

private theorem prime_oneHundredThirtyOneDY_632101 : Nat.Prime 632101 := by norm_num

private theorem prime_oneHundredThirtyOneDY_635707 : Nat.Prime 635707 := by norm_num

private theorem prime_oneHundredThirtyOneDY_642359 : Nat.Prime 642359 := by norm_num

private theorem prime_oneHundredThirtyOneDY_652943 : Nat.Prime 652943 := by norm_num

private theorem prime_oneHundredThirtyOneDY_749129 : Nat.Prime 749129 := by norm_num

private theorem prime_oneHundredThirtyOneDY_780853 : Nat.Prime 780853 := by norm_num

private theorem prime_oneHundredThirtyOneDY_808559 : Nat.Prime 808559 := by norm_num

private theorem prime_oneHundredThirtyOneDY_808651 : Nat.Prime 808651 := by norm_num

private theorem prime_oneHundredThirtyOneDY_850337 : Nat.Prime 850337 := by norm_num

private theorem prime_oneHundredThirtyOneDY_863521 : Nat.Prime 863521 := by norm_num

private theorem prime_oneHundredThirtyOneDY_901403 : Nat.Prime 901403 := by norm_num

private theorem prime_oneHundredThirtyOneDY_959831 : Nat.Prime 959831 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1090807 : Nat.Prime 1090807 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1125571 : Nat.Prime 1125571 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1130287 : Nat.Prime 1130287 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1151599 : Nat.Prime 1151599 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1189219 : Nat.Prime 1189219 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1262741 : Nat.Prime 1262741 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1264877 : Nat.Prime 1264877 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1304267 : Nat.Prime 1304267 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1457213 : Nat.Prime 1457213 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1738003 : Nat.Prime 1738003 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1764089 : Nat.Prime 1764089 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1772297 : Nat.Prime 1772297 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1853207 : Nat.Prime 1853207 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1912741 : Nat.Prime 1912741 := by norm_num

private theorem prime_oneHundredThirtyOneDY_1919377 : Nat.Prime 1919377 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2032553 : Nat.Prime 2032553 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2171881 : Nat.Prime 2171881 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2240213 : Nat.Prime 2240213 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2409829 : Nat.Prime 2409829 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2450219 : Nat.Prime 2450219 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2551933 : Nat.Prime 2551933 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2620901 : Nat.Prime 2620901 := by norm_num

private theorem prime_oneHundredThirtyOneDY_2658049 : Nat.Prime 2658049 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3303523 : Nat.Prime 3303523 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3314651 : Nat.Prime 3314651 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3325687 : Nat.Prime 3325687 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3477967 : Nat.Prime 3477967 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3555311 : Nat.Prime 3555311 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3586727 : Nat.Prime 3586727 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3607607 : Nat.Prime 3607607 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3882643 : Nat.Prime 3882643 := by norm_num

private theorem prime_oneHundredThirtyOneDY_3940451 : Nat.Prime 3940451 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4220653 : Nat.Prime 4220653 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4308961 : Nat.Prime 4308961 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4476631 : Nat.Prime 4476631 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4487407 : Nat.Prime 4487407 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4625431 : Nat.Prime 4625431 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4662433 : Nat.Prime 4662433 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4774261 : Nat.Prime 4774261 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4792331 : Nat.Prime 4792331 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4945711 : Nat.Prime 4945711 := by norm_num

private theorem prime_oneHundredThirtyOneDY_4988143 : Nat.Prime 4988143 := by norm_num

private theorem prime_oneHundredThirtyOneDY_5672011 : Nat.Prime 5672011 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6017159 : Nat.Prime 6017159 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6175259 : Nat.Prime 6175259 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6448609 : Nat.Prime 6448609 := by norm_num

private theorem prime_oneHundredThirtyOneDY_6929723 : Nat.Prime 6929723 := by norm_num

private theorem prime_oneHundredThirtyOneDY_7130119 : Nat.Prime 7130119 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8063053 : Nat.Prime 8063053 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8179487 : Nat.Prime 8179487 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8595383 : Nat.Prime 8595383 := by norm_num

private theorem prime_oneHundredThirtyOneDY_8749921 : Nat.Prime 8749921 := by norm_num

private theorem prime_oneHundredThirtyOneDY_9301679 : Nat.Prime 9301679 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10286779 : Nat.Prime 10286779 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10477963 : Nat.Prime 10477963 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10640293 : Nat.Prime 10640293 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10687007 : Nat.Prime 10687007 := by norm_num

private theorem prime_oneHundredThirtyOneDY_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13099727 : Nat.Prime 13099727 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13671143 : Nat.Prime 13671143 := by norm_num

private theorem prime_oneHundredThirtyOneDY_13709387 : Nat.Prime 13709387 := by norm_num

private theorem prime_oneHundredThirtyOneDY_14284537 : Nat.Prime 14284537 := by norm_num

private theorem prime_oneHundredThirtyOneDY_14595311 : Nat.Prime 14595311 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17013851 : Nat.Prime 17013851 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17459773 : Nat.Prime 17459773 := by norm_num

private theorem prime_oneHundredThirtyOneDY_17629589 : Nat.Prime 17629589 := by norm_num

private theorem prime_oneHundredThirtyOneDY_18462481 : Nat.Prime 18462481 := by norm_num

private theorem prime_oneHundredThirtyOneDY_21315509 : Nat.Prime 21315509 := by norm_num

private theorem prime_oneHundredThirtyOneDY_23930939 : Nat.Prime 23930939 := by norm_num

private theorem prime_oneHundredThirtyOneDY_25305101 : Nat.Prime 25305101 := by norm_num

private theorem prime_oneHundredThirtyOneDY_27886303 : Nat.Prime 27886303 := by norm_num

private theorem prime_oneHundredThirtyOneDY_28015157 : Nat.Prime 28015157 := by norm_num

private theorem prime_oneHundredThirtyOneDY_28392127 : Nat.Prime 28392127 := by norm_num

private theorem prime_oneHundredThirtyOneDY_28438057 : Nat.Prime 28438057 := by norm_num

private theorem prime_oneHundredThirtyOneDY_33104089 : Nat.Prime 33104089 := by
  apply lucas_primality 33104089 (11 : ZMod 33104089)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (107, 1), (4297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (107, 1), (4297, 1)] : List FactorBlock).map factorBlockValue).prod) = 33104089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_107
      · exact prime_oneHundredThirtyOneDY_4297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 33104089) ^ 16552044 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33104089) ^ 11034696 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33104089) ^ 309384 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 33104089) ^ 7704 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_33485281 : Nat.Prime 33485281 := by
  apply lucas_primality 33485281 (17 : ZMod 33485281)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (69761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (69761, 1)] : List FactorBlock).map factorBlockValue).prod) = 33485281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_69761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 33485281) ^ 16742640 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 33485281) ^ 11161760 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 33485281) ^ 6697056 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 33485281) ^ 480 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_34063489 : Nat.Prime 34063489 := by
  apply lucas_primality 34063489 (7 : ZMod 34063489)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (29569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (29569, 1)] : List FactorBlock).map factorBlockValue).prod) = 34063489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_29569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34063489) ^ 17031744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 34063489) ^ 11354496 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 34063489) ^ 1152 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_40471351 : Nat.Prime 40471351 := by
  apply lucas_primality 40471351 (3 : ZMod 40471351)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (67, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (67, 1), (4027, 1)] : List FactorBlock).map factorBlockValue).prod) = 40471351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_67
      · exact prime_oneHundredThirtyOneDY_4027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 40471351) ^ 20235675 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40471351) ^ 13490450 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40471351) ^ 8094270 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40471351) ^ 604050 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 40471351) ^ 10050 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_40966801 : Nat.Prime 40966801 := by
  apply lucas_primality 40966801 (11 : ZMod 40966801)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (7, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (7, 1), (4877, 1)] : List FactorBlock).map factorBlockValue).prod) = 40966801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_4877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 40966801) ^ 20483400 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 40966801) ^ 13655600 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 40966801) ^ 8193360 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 40966801) ^ 5852400 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 40966801) ^ 8400 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_41021861 : Nat.Prime 41021861 := by
  apply lucas_primality 41021861 (2 : ZMod 41021861)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (199, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (199, 1), (937, 1)] : List FactorBlock).map factorBlockValue).prod) = 41021861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_199
      · exact prime_oneHundredThirtyOneDY_937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41021861) ^ 20510930 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41021861) ^ 8204372 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41021861) ^ 3729260 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41021861) ^ 206140 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 41021861) ^ 43780 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_50075401 : Nat.Prime 50075401 := by
  apply lucas_primality 50075401 (11 : ZMod 50075401)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (83459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (83459, 1)] : List FactorBlock).map factorBlockValue).prod) = 50075401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_83459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 50075401) ^ 25037700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 50075401) ^ 16691800 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 50075401) ^ 10015080 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 50075401) ^ 600 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_50117909 : Nat.Prime 50117909 := by
  apply lucas_primality 50117909 (2 : ZMod 50117909)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (305597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (305597, 1)] : List FactorBlock).map factorBlockValue).prod) = 50117909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_305597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50117909) ^ 25058954 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117909) ^ 1222388 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 50117909) ^ 164 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_58933097 : Nat.Prime 58933097 := by
  apply lucas_primality 58933097 (3 : ZMod 58933097)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (101, 1), (72937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (101, 1), (72937, 1)] : List FactorBlock).map factorBlockValue).prod) = 58933097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_101
      · exact prime_oneHundredThirtyOneDY_72937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 58933097) ^ 29466548 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58933097) ^ 583496 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 58933097) ^ 808 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_60611569 : Nat.Prime 60611569 := by
  apply lucas_primality 60611569 (22 : ZMod 60611569)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (1262741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (1262741, 1)] : List FactorBlock).map factorBlockValue).prod) = 60611569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_1262741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (22 : ZMod 60611569) ^ 30305784 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 60611569) ^ 20203856 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 60611569) ^ 48 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_68943377 : Nat.Prime 68943377 := by
  apply lucas_primality 68943377 (3 : ZMod 68943377)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4308961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4308961, 1)] : List FactorBlock).map factorBlockValue).prod) = 68943377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_4308961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 68943377) ^ 34471688 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 68943377) ^ 16 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_73615099 : Nat.Prime 73615099 := by
  apply lucas_primality 73615099 (2 : ZMod 73615099)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (73, 1), (168071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (73, 1), (168071, 1)] : List FactorBlock).map factorBlockValue).prod) = 73615099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_73
      · exact prime_oneHundredThirtyOneDY_168071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 73615099) ^ 36807549 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73615099) ^ 24538366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73615099) ^ 1008426 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 73615099) ^ 438 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_79718591 : Nat.Prime 79718591 := by
  apply lucas_primality 79718591 (7 : ZMod 79718591)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (162691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (162691, 1)] : List FactorBlock).map factorBlockValue).prod) = 79718591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_162691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 79718591) ^ 39859295 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 79718591) ^ 15943718 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 79718591) ^ 11388370 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 79718591) ^ 490 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_80630531 : Nat.Prime 80630531 := by
  apply lucas_primality 80630531 (2 : ZMod 80630531)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8063053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8063053, 1)] : List FactorBlock).map factorBlockValue).prod) = 80630531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_8063053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 80630531) ^ 40315265 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 80630531) ^ 16126106 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 80630531) ^ 10 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_85418147 : Nat.Prime 85418147 := by
  apply lucas_primality 85418147 (2 : ZMod 85418147)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (3882643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (3882643, 1)] : List FactorBlock).map factorBlockValue).prod) = 85418147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_3882643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 85418147) ^ 42709073 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85418147) ^ 7765286 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85418147) ^ 22 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_85496533 : Nat.Prime 85496533 := by
  apply lucas_primality 85496533 (2 : ZMod 85496533)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (787, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (787, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 85496533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_787
      · exact prime_oneHundredThirtyOneDY_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 85496533) ^ 42748266 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85496533) ^ 28498844 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85496533) ^ 7772412 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85496533) ^ 108636 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 85496533) ^ 103884 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_95002183 : Nat.Prime 95002183 := by
  apply lucas_primality 95002183 (3 : ZMod 95002183)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 2), (53, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 2), (53, 1), (823, 1)] : List FactorBlock).map factorBlockValue).prod) = 95002183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_53
      · exact prime_oneHundredThirtyOneDY_823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95002183) ^ 47501091 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95002183) ^ 31667394 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95002183) ^ 8636562 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95002183) ^ 1792494 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95002183) ^ 115434 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_96753101 : Nat.Prime 96753101 := by
  apply lucas_primality 96753101 (2 : ZMod 96753101)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (83, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (83, 1), (11657, 1)] : List FactorBlock).map factorBlockValue).prod) = 96753101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_83
      · exact prime_oneHundredThirtyOneDY_11657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96753101) ^ 48376550 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 96753101) ^ 19350620 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 96753101) ^ 1165700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 96753101) ^ 8300 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_98172631 : Nat.Prime 98172631 := by
  apply lucas_primality 98172631 (6 : ZMod 98172631)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (1090807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (1090807, 1)] : List FactorBlock).map factorBlockValue).prod) = 98172631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_1090807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 98172631) ^ 49086315 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98172631) ^ 32724210 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98172631) ^ 19634526 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 98172631) ^ 90 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_105350503 : Nat.Prime 105350503 := by
  apply lucas_primality 105350503 (6 : ZMod 105350503)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (877, 1), (20021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (877, 1), (20021, 1)] : List FactorBlock).map factorBlockValue).prod) = 105350503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_877
      · exact prime_oneHundredThirtyOneDY_20021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 105350503) ^ 52675251 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 105350503) ^ 35116834 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 105350503) ^ 120126 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 105350503) ^ 5262 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_106249669 : Nat.Prime 106249669 := by
  apply lucas_primality 106249669 (2 : ZMod 106249669)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1264877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1264877, 1)] : List FactorBlock).map factorBlockValue).prod) = 106249669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_1264877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106249669) ^ 53124834 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106249669) ^ 35416556 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106249669) ^ 15178524 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106249669) ^ 84 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_111965743 : Nat.Prime 111965743 := by
  apply lucas_primality 111965743 (3 : ZMod 111965743)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (97, 1), (9161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (97, 1), (9161, 1)] : List FactorBlock).map factorBlockValue).prod) = 111965743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_97
      · exact prime_oneHundredThirtyOneDY_9161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 111965743) ^ 55982871 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 111965743) ^ 37321914 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 111965743) ^ 15995106 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 111965743) ^ 1154286 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 111965743) ^ 12222 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_112364519 : Nat.Prime 112364519 := by
  apply lucas_primality 112364519 (7 : ZMod 112364519)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (41, 1), (10303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (41, 1), (10303, 1)] : List FactorBlock).map factorBlockValue).prod) = 112364519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_10303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 112364519) ^ 56182259 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 112364519) ^ 16052074 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 112364519) ^ 5913922 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 112364519) ^ 2740598 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 112364519) ^ 10906 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_114870583 : Nat.Prime 114870583 := by
  apply lucas_primality 114870583 (3 : ZMod 114870583)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (79, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (79, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) = 114870583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_26927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 114870583) ^ 57435291 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114870583) ^ 38290194 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114870583) ^ 1454058 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 114870583) ^ 4266 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_116001763 : Nat.Prime 116001763 := by
  apply lucas_primality 116001763 (11 : ZMod 116001763)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4027, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4027, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) = 116001763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_4027
      · exact prime_oneHundredThirtyOneDY_4801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 116001763) ^ 58000881 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 116001763) ^ 38667254 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 116001763) ^ 28806 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 116001763) ^ 24162 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_122100373 : Nat.Prime 122100373 := by
  apply lucas_primality 122100373 (2 : ZMod 122100373)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (376853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (376853, 1)] : List FactorBlock).map factorBlockValue).prod) = 122100373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_376853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 122100373) ^ 61050186 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 122100373) ^ 40700124 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 122100373) ^ 324 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_127096967 : Nat.Prime 127096967 := by
  apply lucas_primality 127096967 (5 : ZMod 127096967)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 2), (41, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 2), (41, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 127096967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_97
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 127096967) ^ 63548483 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127096967) ^ 6689314 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127096967) ^ 4382654 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127096967) ^ 3099926 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 127096967) ^ 1310278 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_131008721 : Nat.Prime 131008721 := by
  apply lucas_primality 131008721 (3 : ZMod 131008721)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (73, 1), (22433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (73, 1), (22433, 1)] : List FactorBlock).map factorBlockValue).prod) = 131008721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_73
      · exact prime_oneHundredThirtyOneDY_22433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 131008721) ^ 65504360 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 131008721) ^ 26201744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 131008721) ^ 1794640 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 131008721) ^ 5840 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_137849183 : Nat.Prime 137849183 := by
  apply lucas_primality 137849183 (5 : ZMod 137849183)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3259, 1), (21149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3259, 1), (21149, 1)] : List FactorBlock).map factorBlockValue).prod) = 137849183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3259
      · exact prime_oneHundredThirtyOneDY_21149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 137849183) ^ 68924591 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 137849183) ^ 42298 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 137849183) ^ 6518 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_138783881 : Nat.Prime 138783881 := by
  apply lucas_primality 138783881 (3 : ZMod 138783881)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (383, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (383, 1), (9059, 1)] : List FactorBlock).map factorBlockValue).prod) = 138783881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_383
      · exact prime_oneHundredThirtyOneDY_9059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 138783881) ^ 69391940 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 138783881) ^ 27756776 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 138783881) ^ 362360 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 138783881) ^ 15320 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_143009131 : Nat.Prime 143009131 := by
  apply lucas_primality 143009131 (11 : ZMod 143009131)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (433361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (433361, 1)] : List FactorBlock).map factorBlockValue).prod) = 143009131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_433361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 143009131) ^ 71504565 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 143009131) ^ 47669710 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 143009131) ^ 28601826 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 143009131) ^ 13000830 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 143009131) ^ 330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_161261063 : Nat.Prime 161261063 := by
  apply lucas_primality 161261063 (5 : ZMod 161261063)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80630531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80630531, 1)] : List FactorBlock).map factorBlockValue).prod) = 161261063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_80630531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 161261063) ^ 80630531 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 161261063) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_164215421 : Nat.Prime 164215421 := by
  apply lucas_primality 164215421 (2 : ZMod 164215421)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (787, 1), (10433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (787, 1), (10433, 1)] : List FactorBlock).map factorBlockValue).prod) = 164215421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_787
      · exact prime_oneHundredThirtyOneDY_10433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 164215421) ^ 82107710 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 164215421) ^ 32843084 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 164215421) ^ 208660 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 164215421) ^ 15740 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_169246733 : Nat.Prime 169246733 := by
  apply lucas_primality 169246733 (2 : ZMod 169246733)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (37, 2), (997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (37, 2), (997, 1)] : List FactorBlock).map factorBlockValue).prod) = 169246733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 169246733) ^ 84623366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 169246733) ^ 5459572 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 169246733) ^ 4574236 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 169246733) ^ 169756 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_224729039 : Nat.Prime 224729039 := by
  apply lucas_primality 224729039 (13 : ZMod 224729039)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (112364519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (112364519, 1)] : List FactorBlock).map factorBlockValue).prod) = 224729039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_112364519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 224729039) ^ 112364519 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 224729039) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_235474469 : Nat.Prime 235474469 := by
  apply lucas_primality 235474469 (2 : ZMod 235474469)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2801, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2801, 1), (21017, 1)] : List FactorBlock).map factorBlockValue).prod) = 235474469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_2801
      · exact prime_oneHundredThirtyOneDY_21017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 235474469) ^ 117737234 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 235474469) ^ 84068 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 235474469) ^ 11204 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_238369063 : Nat.Prime 238369063 := by
  apply lucas_primality 238369063 (3 : ZMod 238369063)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2281, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2281, 1), (17417, 1)] : List FactorBlock).map factorBlockValue).prod) = 238369063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_2281
      · exact prime_oneHundredThirtyOneDY_17417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 238369063) ^ 119184531 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 238369063) ^ 79456354 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 238369063) ^ 104502 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 238369063) ^ 13686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_249703477 : Nat.Prime 249703477 := by
  apply lucas_primality 249703477 (2 : ZMod 249703477)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (157, 1), (12049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (157, 1), (12049, 1)] : List FactorBlock).map factorBlockValue).prod) = 249703477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_157
      · exact prime_oneHundredThirtyOneDY_12049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 249703477) ^ 124851738 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249703477) ^ 83234492 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249703477) ^ 22700316 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249703477) ^ 1590468 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 249703477) ^ 20724 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_254513179 : Nat.Prime 254513179 := by
  apply lucas_primality 254513179 (2 : ZMod 254513179)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (47, 1), (33427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (47, 1), (33427, 1)] : List FactorBlock).map factorBlockValue).prod) = 254513179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_33427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 254513179) ^ 127256589 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254513179) ^ 84837726 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254513179) ^ 5415174 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254513179) ^ 7614 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_260132777 : Nat.Prime 260132777 := by
  apply lucas_primality 260132777 (3 : ZMod 260132777)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (1912741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (1912741, 1)] : List FactorBlock).map factorBlockValue).prod) = 260132777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_1912741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 260132777) ^ 130066388 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 260132777) ^ 15301928 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 260132777) ^ 136 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_262017443 : Nat.Prime 262017443 := by
  apply lucas_primality 262017443 (2 : ZMod 262017443)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131008721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131008721, 1)] : List FactorBlock).map factorBlockValue).prod) = 262017443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_131008721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 262017443) ^ 131008721 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 262017443) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_271180309 : Nat.Prime 271180309 := by
  apply lucas_primality 271180309 (6 : ZMod 271180309)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (461191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (461191, 1)] : List FactorBlock).map factorBlockValue).prod) = 271180309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_461191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 271180309) ^ 135590154 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 271180309) ^ 90393436 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 271180309) ^ 38740044 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 271180309) ^ 588 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_282266839 : Nat.Prime 282266839 := by
  apply lucas_primality 282266839 (7 : ZMod 282266839)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2240213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2240213, 1)] : List FactorBlock).map factorBlockValue).prod) = 282266839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_2240213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 282266839) ^ 141133419 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 282266839) ^ 94088946 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 282266839) ^ 40323834 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 282266839) ^ 126 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_288066281 : Nat.Prime 288066281 := by
  apply lucas_primality 288066281 (3 : ZMod 288066281)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (103, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (103, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 288066281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_2411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 288066281) ^ 144033140 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 288066281) ^ 57613256 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 288066281) ^ 9933320 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 288066281) ^ 2796760 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 288066281) ^ 119480 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_302143273 : Nat.Prime 302143273 := by
  apply lucas_primality 302143273 (5 : ZMod 302143273)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (23, 1), (547361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (23, 1), (547361, 1)] : List FactorBlock).map factorBlockValue).prod) = 302143273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_547361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 302143273) ^ 151071636 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 302143273) ^ 100714424 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 302143273) ^ 13136664 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 302143273) ^ 552 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_309727861 : Nat.Prime 309727861 := by
  apply lucas_primality 309727861 (2 : ZMod 309727861)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (109, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (109, 1), (3643, 1)] : List FactorBlock).map factorBlockValue).prod) = 309727861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_109
      · exact prime_oneHundredThirtyOneDY_3643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 309727861) ^ 154863930 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 309727861) ^ 103242620 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 309727861) ^ 61945572 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 309727861) ^ 23825220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 309727861) ^ 2841540 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 309727861) ^ 85020 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_313277771 : Nat.Prime 313277771 := by
  apply lucas_primality 313277771 (2 : ZMod 313277771)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (2409829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (2409829, 1)] : List FactorBlock).map factorBlockValue).prod) = 313277771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_2409829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 313277771) ^ 156638885 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 313277771) ^ 62655554 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 313277771) ^ 24098290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 313277771) ^ 130 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_322223917 : Nat.Prime 322223917 := by
  apply lucas_primality 322223917 (5 : ZMod 322223917)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (4801, 1)] : List FactorBlock).map factorBlockValue).prod) = 322223917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_4801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 322223917) ^ 161111958 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322223917) ^ 107407972 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322223917) ^ 46031988 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322223917) ^ 18954348 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322223917) ^ 6855828 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322223917) ^ 67116 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_322522127 : Nat.Prime 322522127 := by
  apply lucas_primality 322522127 (5 : ZMod 322522127)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (161261063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (161261063, 1)] : List FactorBlock).map factorBlockValue).prod) = 322522127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_161261063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 322522127) ^ 161261063 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 322522127) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_429372389 : Nat.Prime 429372389 := by
  apply lucas_primality 429372389 (2 : ZMod 429372389)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3583, 1), (29959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3583, 1), (29959, 1)] : List FactorBlock).map factorBlockValue).prod) = 429372389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3583
      · exact prime_oneHundredThirtyOneDY_29959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 429372389) ^ 214686194 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 429372389) ^ 119836 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 429372389) ^ 14332 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_470948939 : Nat.Prime 470948939 := by
  apply lucas_primality 470948939 (2 : ZMod 470948939)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (235474469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (235474469, 1)] : List FactorBlock).map factorBlockValue).prod) = 470948939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_235474469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 470948939) ^ 235474469 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 470948939) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_535606919 : Nat.Prime 535606919 := by
  apply lucas_primality 535606919 (7 : ZMod 535606919)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (3477967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (3477967, 1)] : List FactorBlock).map factorBlockValue).prod) = 535606919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_3477967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 535606919) ^ 267803459 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 535606919) ^ 76515274 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 535606919) ^ 48691538 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 535606919) ^ 154 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_542501933 : Nat.Prime 542501933 := by
  apply lucas_primality 542501933 (2 : ZMod 542501933)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (43, 1), (59, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (43, 1), (59, 1), (1091, 1)] : List FactorBlock).map factorBlockValue).prod) = 542501933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_43
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_1091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 542501933) ^ 271250966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542501933) ^ 77500276 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542501933) ^ 12616324 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542501933) ^ 9194948 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 542501933) ^ 497252 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_612498637 : Nat.Prime 612498637 := by
  apply lucas_primality 612498637 (5 : ZMod 612498637)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17013851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17013851, 1)] : List FactorBlock).map factorBlockValue).prod) = 612498637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17013851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 612498637) ^ 306249318 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 612498637) ^ 204166212 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 612498637) ^ 36 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_624082649 : Nat.Prime 624082649 := by
  apply lucas_primality 624082649 (3 : ZMod 624082649)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (17, 1), (41, 1), (59, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (17, 1), (41, 1), (59, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 624082649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 624082649) ^ 312041324 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 624082649) ^ 89154664 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 624082649) ^ 36710744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 624082649) ^ 15221528 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 624082649) ^ 10577672 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 624082649) ^ 2302888 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_626987411 : Nat.Prime 626987411 := by
  apply lucas_primality 626987411 (2 : ZMod 626987411)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (419, 1), (21377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (419, 1), (21377, 1)] : List FactorBlock).map factorBlockValue).prod) = 626987411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_419
      · exact prime_oneHundredThirtyOneDY_21377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 626987411) ^ 313493705 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 626987411) ^ 125397482 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 626987411) ^ 89569630 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 626987411) ^ 1496390 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 626987411) ^ 29330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17203
      · exact prime_oneHundredThirtyOneDY_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_756566593 : Nat.Prime 756566593 := by
  apply lucas_primality 756566593 (5 : ZMod 756566593)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (3940451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (3940451, 1)] : List FactorBlock).map factorBlockValue).prod) = 756566593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_3940451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 756566593) ^ 378283296 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 756566593) ^ 252188864 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 756566593) ^ 192 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_859540321 : Nat.Prime 859540321 := by
  apply lucas_primality 859540321 (11 : ZMod 859540321)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (59, 1), (67, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (59, 1), (67, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 859540321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_67
      · exact prime_oneHundredThirtyOneDY_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 859540321) ^ 429770160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 859540321) ^ 286513440 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 859540321) ^ 171908064 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 859540321) ^ 14568480 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 859540321) ^ 12828960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 859540321) ^ 5692320 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1028307307 : Nat.Prime 1028307307 := by
  apply lucas_primality 1028307307 (2 : ZMod 1028307307)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (41, 1), (321547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (41, 1), (321547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1028307307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_321547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1028307307) ^ 514153653 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028307307) ^ 342769102 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028307307) ^ 79100562 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028307307) ^ 25080666 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1028307307) ^ 3198 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1047586381 : Nat.Prime 1047586381 := by
  apply lucas_primality 1047586381 (10 : ZMod 1047586381)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (17459773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (17459773, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047586381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_17459773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1047586381) ^ 523793190 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1047586381) ^ 349195460 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1047586381) ^ 209517276 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1047586381) ^ 60 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1071768767 : Nat.Prime 1071768767 := by
  apply lucas_primality 1071768767 (5 : ZMod 1071768767)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (31, 1), (103, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (31, 1), (103, 1), (7297, 1)] : List FactorBlock).map factorBlockValue).prod) = 1071768767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_7297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1071768767) ^ 535884383 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071768767) ^ 46598642 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071768767) ^ 34573186 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071768767) ^ 10405522 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1071768767) ^ 146878 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1084721237 : Nat.Prime 1084721237 := by
  apply lucas_primality 1084721237 (2 : ZMod 1084721237)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (271180309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (271180309, 1)] : List FactorBlock).map factorBlockValue).prod) = 1084721237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_271180309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1084721237) ^ 542360618 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084721237) ^ 4 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1085003867 : Nat.Prime 1085003867 := by
  apply lucas_primality 1085003867 (2 : ZMod 1085003867)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (542501933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (542501933, 1)] : List FactorBlock).map factorBlockValue).prod) = 1085003867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_542501933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1085003867) ^ 542501933 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1085003867) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1109917829 : Nat.Prime 1109917829 := by
  apply lucas_primality 1109917829 (2 : ZMod 1109917829)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (2309, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (2309, 1), (7069, 1)] : List FactorBlock).map factorBlockValue).prod) = 1109917829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_2309
      · exact prime_oneHundredThirtyOneDY_7069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1109917829) ^ 554958914 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109917829) ^ 65289284 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109917829) ^ 480692 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1109917829) ^ 157012 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1163513123 : Nat.Prime 1163513123 := by
  apply lucas_primality 1163513123 (2 : ZMod 1163513123)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (719, 1), (5821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (719, 1), (5821, 1)] : List FactorBlock).map factorBlockValue).prod) = 1163513123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_139
      · exact prime_oneHundredThirtyOneDY_719
      · exact prime_oneHundredThirtyOneDY_5821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1163513123) ^ 581756561 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1163513123) ^ 8370598 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1163513123) ^ 1618238 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1163513123) ^ 199882 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1183619911 : Nat.Prime 1183619911 := by
  apply lucas_primality 1183619911 (6 : ZMod 1183619911)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (3586727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (3586727, 1)] : List FactorBlock).map factorBlockValue).prod) = 1183619911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_3586727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1183619911) ^ 591809955 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1183619911) ^ 394539970 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1183619911) ^ 236723982 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1183619911) ^ 107601810 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1183619911) ^ 330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1264536997 : Nat.Prime 1264536997 := by
  apply lucas_primality 1264536997 (5 : ZMod 1264536997)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (31, 1), (251, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (31, 1), (251, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1264536997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_251
      · exact prime_oneHundredThirtyOneDY_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1264536997) ^ 632268498 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264536997) ^ 421512332 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264536997) ^ 43604724 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264536997) ^ 40791516 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264536997) ^ 5037996 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1264536997) ^ 2707788 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1343494939 : Nat.Prime 1343494939 := by
  apply lucas_primality 1343494939 (3 : ZMod 1343494939)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (83, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (83, 1), (4289, 1)] : List FactorBlock).map factorBlockValue).prod) = 1343494939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_83
      · exact prime_oneHundredThirtyOneDY_4289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1343494939) ^ 671747469 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343494939) ^ 447831646 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343494939) ^ 79029114 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343494939) ^ 36310674 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343494939) ^ 16186686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1343494939) ^ 313242 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1373146543 : Nat.Prime 1373146543 := by
  apply lucas_primality 1373146543 (6 : ZMod 1373146543)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (4487407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (4487407, 1)] : List FactorBlock).map factorBlockValue).prod) = 1373146543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_4487407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1373146543) ^ 686573271 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1373146543) ^ 457715514 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1373146543) ^ 80773326 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1373146543) ^ 306 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1568916263 : Nat.Prime 1568916263 := by
  apply lucas_primality 1568916263 (5 : ZMod 1568916263)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (25305101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (25305101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1568916263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_25305101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1568916263) ^ 784458131 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568916263) ^ 50610202 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1568916263) ^ 62 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1613137927 : Nat.Prime 1613137927 := by
  apply lucas_primality 1613137927 (3 : ZMod 1613137927)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (647, 1), (415543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (647, 1), (415543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1613137927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_647
      · exact prime_oneHundredThirtyOneDY_415543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1613137927) ^ 806568963 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613137927) ^ 537712642 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613137927) ^ 2493258 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1613137927) ^ 3882 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1694133731 : Nat.Prime 1694133731 := by
  apply lucas_primality 1694133731 (2 : ZMod 1694133731)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (599, 1), (282827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (599, 1), (282827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694133731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_599
      · exact prime_oneHundredThirtyOneDY_282827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1694133731) ^ 847066865 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1694133731) ^ 338826746 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1694133731) ^ 2828270 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1694133731) ^ 5990 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1840664927 : Nat.Prime 1840664927 := by
  apply lucas_primality 1840664927 (5 : ZMod 1840664927)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1021, 1), (901403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1021, 1), (901403, 1)] : List FactorBlock).map factorBlockValue).prod) = 1840664927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_1021
      · exact prime_oneHundredThirtyOneDY_901403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1840664927) ^ 920332463 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1840664927) ^ 1802806 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1840664927) ^ 2042 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2418038627 : Nat.Prime 2418038627 := by
  apply lucas_primality 2418038627 (2 : ZMod 2418038627)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (1471, 1), (26513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (1471, 1), (26513, 1)] : List FactorBlock).map factorBlockValue).prod) = 2418038627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_1471
      · exact prime_oneHundredThirtyOneDY_26513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2418038627) ^ 1209019313 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418038627) ^ 78001246 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418038627) ^ 1643806 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2418038627) ^ 91202 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2502913367 : Nat.Prime 2502913367 := by
  apply lucas_primality 2502913367 (5 : ZMod 2502913367)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (73615099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (73615099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2502913367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_73615099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2502913367) ^ 1251456683 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2502913367) ^ 147230198 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2502913367) ^ 34 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2546711047 : Nat.Prime 2546711047 := by
  apply lucas_primality 2546711047 (3 : ZMod 2546711047)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (59, 1), (218003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (59, 1), (218003, 1)] : List FactorBlock).map factorBlockValue).prod) = 2546711047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_218003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2546711047) ^ 1273355523 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546711047) ^ 848903682 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546711047) ^ 231519186 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546711047) ^ 43164594 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2546711047) ^ 11682 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2630012113 : Nat.Prime 2630012113 := by
  apply lucas_primality 2630012113 (5 : ZMod 2630012113)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (13, 1), (149, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (13, 1), (149, 1), (449, 1)] : List FactorBlock).map factorBlockValue).prod) = 2630012113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_149
      · exact prime_oneHundredThirtyOneDY_449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2630012113) ^ 1315006056 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2630012113) ^ 876670704 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2630012113) ^ 375716016 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2630012113) ^ 202308624 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2630012113) ^ 17651088 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2630012113) ^ 5857488 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2698543763 : Nat.Prime 2698543763 := by
  apply lucas_primality 2698543763 (2 : ZMod 2698543763)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (13099727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (13099727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2698543763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_13099727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2698543763) ^ 1349271881 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2698543763) ^ 26199454 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2698543763) ^ 206 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2848755499 : Nat.Prime 2848755499 := by
  apply lucas_primality 2848755499 (2 : ZMod 2848755499)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1307, 1), (363269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1307, 1), (363269, 1)] : List FactorBlock).map factorBlockValue).prod) = 2848755499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_1307
      · exact prime_oneHundredThirtyOneDY_363269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2848755499) ^ 1424377749 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848755499) ^ 949585166 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848755499) ^ 2179614 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2848755499) ^ 7842 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2864002171 : Nat.Prime 2864002171 := by
  apply lucas_primality 2864002171 (2 : ZMod 2864002171)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (211, 1), (373, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (211, 1), (373, 1), (1213, 1)] : List FactorBlock).map factorBlockValue).prod) = 2864002171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_211
      · exact prime_oneHundredThirtyOneDY_373
      · exact prime_oneHundredThirtyOneDY_1213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2864002171) ^ 1432001085 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864002171) ^ 954667390 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864002171) ^ 572800434 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864002171) ^ 13573470 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864002171) ^ 7678290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2864002171) ^ 2361090 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_3018869417 : Nat.Prime 3018869417 := by
  apply lucas_primality 3018869417 (3 : ZMod 3018869417)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (23, 1), (863521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (23, 1), (863521, 1)] : List FactorBlock).map factorBlockValue).prod) = 3018869417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_863521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3018869417) ^ 1509434708 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018869417) ^ 158887864 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018869417) ^ 131255192 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3018869417) ^ 3496 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_3957963721 : Nat.Prime 3957963721 := by
  apply lucas_primality 3957963721 (7 : ZMod 3957963721)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (19, 1), (157, 1), (11057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (19, 1), (157, 1), (11057, 1)] : List FactorBlock).map factorBlockValue).prod) = 3957963721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_157
      · exact prime_oneHundredThirtyOneDY_11057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3957963721) ^ 1978981860 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957963721) ^ 1319321240 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957963721) ^ 791592744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957963721) ^ 208313880 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957963721) ^ 25209960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3957963721) ^ 357960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_3960293977 : Nat.Prime 3960293977 := by
  apply lucas_primality 3960293977 (7 : ZMod 3960293977)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (263, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (263, 1), (5101, 1)] : List FactorBlock).map factorBlockValue).prod) = 3960293977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_263
      · exact prime_oneHundredThirtyOneDY_5101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3960293977) ^ 1980146988 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3960293977) ^ 1320097992 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3960293977) ^ 96592536 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3960293977) ^ 15058152 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 3960293977) ^ 776376 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4183369759 : Nat.Prime 4183369759 := by
  apply lucas_primality 4183369759 (3 : ZMod 4183369759)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (13671143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (13671143, 1)] : List FactorBlock).map factorBlockValue).prod) = 4183369759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_13671143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4183369759) ^ 2091684879 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4183369759) ^ 1394456586 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4183369759) ^ 246080574 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4183369759) ^ 306 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4400415059 : Nat.Prime 4400415059 := by
  apply lucas_primality 4400415059 (2 : ZMod 4400415059)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (169246733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (169246733, 1)] : List FactorBlock).map factorBlockValue).prod) = 4400415059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_169246733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4400415059) ^ 2200207529 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4400415059) ^ 338493466 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4400415059) ^ 26 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4581475081 : Nat.Prime 4581475081 := by
  apply lucas_primality 4581475081 (11 : ZMod 4581475081)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 2), (59, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (7, 1), (13, 2), (59, 1), (547, 1)] : List FactorBlock).map factorBlockValue).prod) = 4581475081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 4581475081) ^ 2290737540 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 1527158360 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 916295016 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 654496440 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 352421160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 77652120 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 4581475081) ^ 8375640 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4689245263 : Nat.Prime 4689245263 := by
  apply lucas_primality 4689245263 (3 : ZMod 4689245263)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (773, 1), (77773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (773, 1), (77773, 1)] : List FactorBlock).map factorBlockValue).prod) = 4689245263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_773
      · exact prime_oneHundredThirtyOneDY_77773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4689245263) ^ 2344622631 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4689245263) ^ 1563081754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4689245263) ^ 360711174 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4689245263) ^ 6066294 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4689245263) ^ 60294 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5185193059 : Nat.Prime 5185193059 := by
  apply lucas_primality 5185193059 (2 : ZMod 5185193059)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (288066281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (288066281, 1)] : List FactorBlock).map factorBlockValue).prod) = 5185193059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_288066281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5185193059) ^ 2592596529 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5185193059) ^ 1728397686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5185193059) ^ 18 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5247251143 : Nat.Prime 5247251143 := by
  apply lucas_primality 5247251143 (3 : ZMod 5247251143)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (23, 1), (89, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (23, 1), (89, 1), (8719, 1)] : List FactorBlock).map factorBlockValue).prod) = 5247251143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_89
      · exact prime_oneHundredThirtyOneDY_8719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5247251143) ^ 2623625571 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5247251143) ^ 1749083714 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5247251143) ^ 749607306 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5247251143) ^ 228141354 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5247251143) ^ 58957878 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5247251143) ^ 601818 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5655420833 : Nat.Prime 5655420833 := by
  apply lucas_primality 5655420833 (3 : ZMod 5655420833)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (9301679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (9301679, 1)] : List FactorBlock).map factorBlockValue).prod) = 5655420833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_9301679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5655420833) ^ 2827710416 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5655420833) ^ 297653728 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5655420833) ^ 608 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7534138099 : Nat.Prime 7534138099 := by
  apply lucas_primality 7534138099 (2 : ZMod 7534138099)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (37, 1), (117431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (37, 1), (117431, 1)] : List FactorBlock).map factorBlockValue).prod) = 7534138099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_117431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7534138099) ^ 3767069049 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7534138099) ^ 2511379366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7534138099) ^ 443184594 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7534138099) ^ 203625354 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7534138099) ^ 64158 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7712109869 : Nat.Prime 7712109869 := by
  apply lucas_primality 7712109869 (2 : ZMod 7712109869)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (41021861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (41021861, 1)] : List FactorBlock).map factorBlockValue).prod) = 7712109869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_41021861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7712109869) ^ 3856054934 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7712109869) ^ 164087444 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7712109869) ^ 188 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7950441791 : Nat.Prime 7950441791 := by
  apply lucas_primality 7950441791 (13 : ZMod 7950441791)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1307, 1), (608297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1307, 1), (608297, 1)] : List FactorBlock).map factorBlockValue).prod) = 7950441791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_1307
      · exact prime_oneHundredThirtyOneDY_608297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 7950441791) ^ 3975220895 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 7950441791) ^ 1590088358 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 7950441791) ^ 6082970 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 7950441791) ^ 13070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_8800830119 : Nat.Prime 8800830119 := by
  apply lucas_primality 8800830119 (7 : ZMod 8800830119)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4400415059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4400415059, 1)] : List FactorBlock).map factorBlockValue).prod) = 8800830119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_4400415059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 8800830119) ^ 4400415059 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 8800830119) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9022269677 : Nat.Prime 9022269677 := by
  apply lucas_primality 9022269677 (2 : ZMod 9022269677)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (322223917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (322223917, 1)] : List FactorBlock).map factorBlockValue).prod) = 9022269677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_322223917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 9022269677) ^ 4511134838 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9022269677) ^ 1288895668 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9022269677) ^ 28 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9523265753 : Nat.Prime 9523265753 := by
  apply lucas_primality 9523265753 (3 : ZMod 9523265753)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (13, 1), (1189219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (13, 1), (1189219, 1)] : List FactorBlock).map factorBlockValue).prod) = 9523265753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_1189219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9523265753) ^ 4761632876 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9523265753) ^ 1360466536 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9523265753) ^ 865751432 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9523265753) ^ 732558904 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 9523265753) ^ 8008 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9856827529 : Nat.Prime 9856827529 := by
  apply lucas_primality 9856827529 (11 : ZMod 9856827529)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (37, 1), (652943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (37, 1), (652943, 1)] : List FactorBlock).map factorBlockValue).prod) = 9856827529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_652943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 9856827529) ^ 4928413764 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 9856827529) ^ 3285609176 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 9856827529) ^ 579813384 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 9856827529) ^ 266400744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 9856827529) ^ 15096 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_11268142777 : Nat.Prime 11268142777 := by
  apply lucas_primality 11268142777 (5 : ZMod 11268142777)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (17, 1), (43, 1), (19463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (17, 1), (43, 1), (19463, 1)] : List FactorBlock).map factorBlockValue).prod) = 11268142777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_43
      · exact prime_oneHundredThirtyOneDY_19463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11268142777) ^ 5634071388 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 11268142777) ^ 3756047592 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 11268142777) ^ 1024376616 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 11268142777) ^ 662831928 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 11268142777) ^ 262049832 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 11268142777) ^ 578952 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_14489593847 : Nat.Prime 14489593847 := by
  apply lucas_primality 14489593847 (5 : ZMod 14489593847)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (13, 1), (479, 1), (166207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (13, 1), (479, 1), (166207, 1)] : List FactorBlock).map factorBlockValue).prod) = 14489593847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_479
      · exact prime_oneHundredThirtyOneDY_166207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 14489593847) ^ 7244796923 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489593847) ^ 2069941978 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489593847) ^ 1114584142 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489593847) ^ 30249674 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 14489593847) ^ 87178 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_14508231763 : Nat.Prime 14508231763 := by
  apply lucas_primality 14508231763 (2 : ZMod 14508231763)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2418038627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2418038627, 1)] : List FactorBlock).map factorBlockValue).prod) = 14508231763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_2418038627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14508231763) ^ 7254115881 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14508231763) ^ 4836077254 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 14508231763) ^ 6 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_14520128771 : Nat.Prime 14520128771 := by
  apply lucas_primality 14520128771 (6 : ZMod 14520128771)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (1439, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (1439, 1), (3067, 1)] : List FactorBlock).map factorBlockValue).prod) = 14520128771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_1439
      · exact prime_oneHundredThirtyOneDY_3067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 14520128771) ^ 7260064385 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 14520128771) ^ 2904025754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 14520128771) ^ 2074304110 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 14520128771) ^ 308938910 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 14520128771) ^ 10090430 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 14520128771) ^ 4734310 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_15129170477 : Nat.Prime 15129170477 := by
  apply lucas_primality 15129170477 (2 : ZMod 15129170477)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (16871, 1), (32027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (16871, 1), (32027, 1)] : List FactorBlock).map factorBlockValue).prod) = 15129170477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_16871
      · exact prime_oneHundredThirtyOneDY_32027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15129170477) ^ 7564585238 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15129170477) ^ 2161310068 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15129170477) ^ 896756 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 15129170477) ^ 472388 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_15471725779 : Nat.Prime 15471725779 := by
  apply lucas_primality 15471725779 (3 : ZMod 15471725779)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (859540321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (859540321, 1)] : List FactorBlock).map factorBlockValue).prod) = 15471725779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_859540321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15471725779) ^ 7735862889 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15471725779) ^ 5157241926 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15471725779) ^ 18 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_16248796139 : Nat.Prime 16248796139 := by
  apply lucas_primality 16248796139 (2 : ZMod 16248796139)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13339, 1), (609071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13339, 1), (609071, 1)] : List FactorBlock).map factorBlockValue).prod) = 16248796139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_13339
      · exact prime_oneHundredThirtyOneDY_609071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 16248796139) ^ 8124398069 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16248796139) ^ 1218142 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16248796139) ^ 26678 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_16765390541 : Nat.Prime 16765390541 := by
  apply lucas_primality 16765390541 (3 : ZMod 16765390541)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13033, 1), (64319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13033, 1), (64319, 1)] : List FactorBlock).map factorBlockValue).prod) = 16765390541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_13033
      · exact prime_oneHundredThirtyOneDY_64319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 16765390541) ^ 8382695270 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 16765390541) ^ 3353078108 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 16765390541) ^ 1286380 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 16765390541) ^ 260660 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_16840911709 : Nat.Prime 16840911709 := by
  apply lucas_primality 16840911709 (6 : ZMod 16840911709)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (127, 1), (523, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (127, 1), (523, 1), (7043, 1)] : List FactorBlock).map factorBlockValue).prod) = 16840911709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_127
      · exact prime_oneHundredThirtyOneDY_523
      · exact prime_oneHundredThirtyOneDY_7043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 16840911709) ^ 8420455854 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16840911709) ^ 5613637236 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16840911709) ^ 132605604 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16840911709) ^ 32200596 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 16840911709) ^ 2391156 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_17787391267 : Nat.Prime 17787391267 := by
  apply lucas_primality 17787391267 (2 : ZMod 17787391267)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (68943377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (68943377, 1)] : List FactorBlock).map factorBlockValue).prod) = 17787391267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_43
      · exact prime_oneHundredThirtyOneDY_68943377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17787391267) ^ 8893695633 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17787391267) ^ 5929130422 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17787391267) ^ 413660262 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17787391267) ^ 258 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_18666142021 : Nat.Prime 18666142021 := by
  apply lucas_primality 18666142021 (11 : ZMod 18666142021)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (2179, 1), (47591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (2179, 1), (47591, 1)] : List FactorBlock).map factorBlockValue).prod) = 18666142021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_2179
      · exact prime_oneHundredThirtyOneDY_47591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 18666142021) ^ 9333071010 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 18666142021) ^ 6222047340 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 18666142021) ^ 3733228404 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 18666142021) ^ 8566380 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 18666142021) ^ 392220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_18937918577 : Nat.Prime 18937918577 := by
  apply lucas_primality 18937918577 (3 : ZMod 18937918577)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (1183619911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (1183619911, 1)] : List FactorBlock).map factorBlockValue).prod) = 18937918577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_1183619911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 18937918577) ^ 9468959288 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 18937918577) ^ 16 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_20840224753 : Nat.Prime 20840224753 := by
  apply lucas_primality 20840224753 (5 : ZMod 20840224753)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (613, 1), (78697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (613, 1), (78697, 1)] : List FactorBlock).map factorBlockValue).prod) = 20840224753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_613
      · exact prime_oneHundredThirtyOneDY_78697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 20840224753) ^ 10420112376 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 20840224753) ^ 6946741584 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 20840224753) ^ 33997104 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 20840224753) ^ 264816 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_23761763863 : Nat.Prime 23761763863 := by
  apply lucas_primality 23761763863 (3 : ZMod 23761763863)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3960293977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3960293977, 1)] : List FactorBlock).map factorBlockValue).prod) = 23761763863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_3960293977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23761763863) ^ 11880881931 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 23761763863) ^ 7920587954 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 23761763863) ^ 6 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_24985046173 : Nat.Prime 24985046173 := by
  apply lucas_primality 24985046173 (2 : ZMod 24985046173)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (41227, 1), (50503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (41227, 1), (50503, 1)] : List FactorBlock).map factorBlockValue).prod) = 24985046173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_41227
      · exact prime_oneHundredThirtyOneDY_50503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24985046173) ^ 12492523086 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24985046173) ^ 8328348724 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24985046173) ^ 606036 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24985046173) ^ 494724 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_31925019293 : Nat.Prime 31925019293 := by
  apply lucas_primality 31925019293 (2 : ZMod 31925019293)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (61, 1), (4220653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (61, 1), (4220653, 1)] : List FactorBlock).map factorBlockValue).prod) = 31925019293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_61
      · exact prime_oneHundredThirtyOneDY_4220653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31925019293) ^ 15962509646 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31925019293) ^ 1029839332 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31925019293) ^ 523360972 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31925019293) ^ 7564 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_32704147823 : Nat.Prime 32704147823 := by
  apply lucas_primality 32704147823 (5 : ZMod 32704147823)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (41, 1), (829, 1), (25321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (41, 1), (829, 1), (25321, 1)] : List FactorBlock).map factorBlockValue).prod) = 32704147823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_829
      · exact prime_oneHundredThirtyOneDY_25321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32704147823) ^ 16352073911 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32704147823) ^ 1721270938 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32704147823) ^ 797662142 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32704147823) ^ 39450118 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32704147823) ^ 1291582 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_46021553833 : Nat.Prime 46021553833 := by
  apply lucas_primality 46021553833 (5 : ZMod 46021553833)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1087, 1), (1764089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1087, 1), (1764089, 1)] : List FactorBlock).map factorBlockValue).prod) = 46021553833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_1087
      · exact prime_oneHundredThirtyOneDY_1764089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 46021553833) ^ 23010776916 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 46021553833) ^ 15340517944 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 46021553833) ^ 42338136 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 46021553833) ^ 26088 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_58168701863 : Nat.Prime 58168701863 := by
  apply lucas_primality 58168701863 (10 : ZMod 58168701863)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1264536997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1264536997, 1)] : List FactorBlock).map factorBlockValue).prod) = 58168701863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_1264536997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 58168701863) ^ 29084350931 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 58168701863) ^ 2529073994 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 58168701863) ^ 46 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_60449148883 : Nat.Prime 60449148883 := by
  apply lucas_primality 60449148883 (2 : ZMod 60449148883)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (157, 1), (7130119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (157, 1), (7130119, 1)] : List FactorBlock).map factorBlockValue).prod) = 60449148883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_157
      · exact prime_oneHundredThirtyOneDY_7130119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 60449148883) ^ 30224574441 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 60449148883) ^ 20149716294 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 60449148883) ^ 385026426 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 60449148883) ^ 8478 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_68202333767 : Nat.Prime 68202333767 := by
  apply lucas_primality 68202333767 (5 : ZMod 68202333767)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (37, 1), (6929723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (37, 1), (6929723, 1)] : List FactorBlock).map factorBlockValue).prod) = 68202333767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_6929723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68202333767) ^ 34101166883 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68202333767) ^ 9743190538 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68202333767) ^ 3589596514 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68202333767) ^ 1843306318 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68202333767) ^ 9842 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_91140324829 : Nat.Prime 91140324829 := by
  apply lucas_primality 91140324829 (2 : ZMod 91140324829)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1085003867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1085003867, 1)] : List FactorBlock).map factorBlockValue).prod) = 91140324829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_1085003867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91140324829) ^ 45570162414 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91140324829) ^ 30380108276 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91140324829) ^ 13020046404 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91140324829) ^ 84 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_109236503707 : Nat.Prime 109236503707 := by
  apply lucas_primality 109236503707 (3 : ZMod 109236503707)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (37, 1), (227, 1), (197059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (37, 1), (227, 1), (197059, 1)] : List FactorBlock).map factorBlockValue).prod) = 109236503707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_227
      · exact prime_oneHundredThirtyOneDY_197059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 109236503707) ^ 54618251853 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 109236503707) ^ 36412167902 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 109236503707) ^ 9930591246 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 109236503707) ^ 2952337938 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 109236503707) ^ 481218078 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 109236503707) ^ 554334 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_133173810229 : Nat.Prime 133173810229 := by
  apply lucas_primality 133173810229 (2 : ZMod 133173810229)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (47, 1), (71, 1), (3325687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (47, 1), (71, 1), (3325687, 1)] : List FactorBlock).map factorBlockValue).prod) = 133173810229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_71
      · exact prime_oneHundredThirtyOneDY_3325687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 133173810229) ^ 66586905114 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 133173810229) ^ 44391270076 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 133173810229) ^ 2833485324 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 133173810229) ^ 1875687468 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 133173810229) ^ 40044 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_141365194987 : Nat.Prime 141365194987 := by
  apply lucas_primality 141365194987 (5 : ZMod 141365194987)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (1069, 1), (373561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (1069, 1), (373561, 1)] : List FactorBlock).map factorBlockValue).prod) = 141365194987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_1069
      · exact prime_oneHundredThirtyOneDY_373561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141365194987) ^ 70682597493 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 141365194987) ^ 47121731662 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 141365194987) ^ 2396020254 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 141365194987) ^ 132240594 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 141365194987) ^ 378426 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_168813452789 : Nat.Prime 168813452789 := by
  apply lucas_primality 168813452789 (2 : ZMod 168813452789)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (164215421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (164215421, 1)] : List FactorBlock).map factorBlockValue).prod) = 168813452789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_257
      · exact prime_oneHundredThirtyOneDY_164215421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 168813452789) ^ 84406726394 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 168813452789) ^ 656861684 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 168813452789) ^ 1028 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_202048084387 : Nat.Prime 202048084387 := by
  apply lucas_primality 202048084387 (3 : ZMod 202048084387)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (66863, 1), (167879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (66863, 1), (167879, 1)] : List FactorBlock).map factorBlockValue).prod) = 202048084387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_66863
      · exact prime_oneHundredThirtyOneDY_167879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 202048084387) ^ 101024042193 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 202048084387) ^ 67349361462 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 202048084387) ^ 3021822 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 202048084387) ^ 1203534 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_209636714207 : Nat.Prime 209636714207 := by
  apply lucas_primality 209636714207 (5 : ZMod 209636714207)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (29, 2), (53, 1), (61, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (29, 2), (53, 1), (61, 1), (2029, 1)] : List FactorBlock).map factorBlockValue).prod) = 209636714207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_53
      · exact prime_oneHundredThirtyOneDY_61
      · exact prime_oneHundredThirtyOneDY_2029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 209636714207) ^ 104818357103 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 209636714207) ^ 11033511274 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 209636714207) ^ 7228852214 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 209636714207) ^ 3955409702 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 209636714207) ^ 3436667446 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 209636714207) ^ 103320214 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_211585285339 : Nat.Prime 211585285339 := by
  apply lucas_primality 211585285339 (2 : ZMod 211585285339)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (29, 1), (389, 1), (446569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (29, 1), (389, 1), (446569, 1)] : List FactorBlock).map factorBlockValue).prod) = 211585285339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_389
      · exact prime_oneHundredThirtyOneDY_446569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 211585285339) ^ 105792642669 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 211585285339) ^ 70528428446 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 211585285339) ^ 30226469334 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 211585285339) ^ 7296044322 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 211585285339) ^ 543921042 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 211585285339) ^ 473802 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_265675555043 : Nat.Prime 265675555043 := by
  apply lucas_primality 265675555043 (2 : ZMod 265675555043)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 3), (3089, 1), (8753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 3), (3089, 1), (8753, 1)] : List FactorBlock).map factorBlockValue).prod) = 265675555043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_3089
      · exact prime_oneHundredThirtyOneDY_8753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 265675555043) ^ 132837777521 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 265675555043) ^ 15627973826 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 265675555043) ^ 86006978 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 265675555043) ^ 30352514 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_273675010793 : Nat.Prime 273675010793 := by
  apply lucas_primality 273675010793 (3 : ZMod 273675010793)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (137, 1), (249703477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (137, 1), (249703477, 1)] : List FactorBlock).map factorBlockValue).prod) = 273675010793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_137
      · exact prime_oneHundredThirtyOneDY_249703477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 273675010793) ^ 136837505396 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273675010793) ^ 1997627816 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273675010793) ^ 1096 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_302084053259 : Nat.Prime 302084053259 := by
  apply lucas_primality 302084053259 (6 : ZMod 302084053259)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (41, 1), (103, 1), (281, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (41, 1), (103, 1), (281, 1), (9791, 1)] : List FactorBlock).map factorBlockValue).prod) = 302084053259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_281
      · exact prime_oneHundredThirtyOneDY_9791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 302084053259) ^ 151042026629 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 302084053259) ^ 23237234866 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 302084053259) ^ 7367903738 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 302084053259) ^ 2932854886 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 302084053259) ^ 1075032218 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 302084053259) ^ 30853238 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_397323349799 : Nat.Prime 397323349799 := by
  apply lucas_primality 397323349799 (19 : ZMod 397323349799)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (331, 1), (2620901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (331, 1), (2620901, 1)] : List FactorBlock).map factorBlockValue).prod) = 397323349799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_229
      · exact prime_oneHundredThirtyOneDY_331
      · exact prime_oneHundredThirtyOneDY_2620901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 397323349799) ^ 198661674899 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (19 : ZMod 397323349799) ^ 1735036462 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (19 : ZMod 397323349799) ^ 1200372658 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (19 : ZMod 397323349799) ^ 151598 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_526859130697 : Nat.Prime 526859130697 := by
  apply lucas_primality 526859130697 (10 : ZMod 526859130697)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (257, 1), (85418147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (257, 1), (85418147, 1)] : List FactorBlock).map factorBlockValue).prod) = 526859130697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_257
      · exact prime_oneHundredThirtyOneDY_85418147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 526859130697) ^ 263429565348 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 526859130697) ^ 175619710232 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 526859130697) ^ 2050035528 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 526859130697) ^ 6168 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_604491488831 : Nat.Prime 604491488831 := by
  apply lucas_primality 604491488831 (17 : ZMod 604491488831)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (60449148883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (60449148883, 1)] : List FactorBlock).map factorBlockValue).prod) = 604491488831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_60449148883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 604491488831) ^ 302245744415 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 604491488831) ^ 120898297766 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 604491488831) ^ 10 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_655419022243 : Nat.Prime 655419022243 := by
  apply lucas_primality 655419022243 (2 : ZMod 655419022243)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (109236503707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (109236503707, 1)] : List FactorBlock).map factorBlockValue).prod) = 655419022243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_109236503707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 655419022243) ^ 327709511121 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 655419022243) ^ 218473007414 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 655419022243) ^ 6 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_848191169923 : Nat.Prime 848191169923 := by
  apply lucas_primality 848191169923 (3 : ZMod 848191169923)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (141365194987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (141365194987, 1)] : List FactorBlock).map factorBlockValue).prod) = 848191169923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_141365194987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 848191169923) ^ 424095584961 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 848191169923) ^ 282730389974 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 848191169923) ^ 6 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_895241128427 : Nat.Prime 895241128427 := by
  apply lucas_primality 895241128427 (2 : ZMod 895241128427)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (107, 1), (4183369759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (107, 1), (4183369759, 1)] : List FactorBlock).map factorBlockValue).prod) = 895241128427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_107
      · exact prime_oneHundredThirtyOneDY_4183369759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 895241128427) ^ 447620564213 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 895241128427) ^ 8366739518 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 895241128427) ^ 214 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1098356388113 : Nat.Prime 1098356388113 := by
  apply lucas_primality 1098356388113 (3 : ZMod 1098356388113)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (59, 1), (1163513123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (59, 1), (1163513123, 1)] : List FactorBlock).map factorBlockValue).prod) = 1098356388113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_1163513123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1098356388113) ^ 549178194056 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098356388113) ^ 18616209968 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1098356388113) ^ 944 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1100405540287 : Nat.Prime 1100405540287 := by
  apply lucas_primality 1100405540287 (5 : ZMod 1100405540287)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (37, 1), (127096967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (37, 1), (127096967, 1)] : List FactorBlock).map factorBlockValue).prod) = 1100405540287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_127096967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1100405540287) ^ 550202770143 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1100405540287) ^ 366801846762 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1100405540287) ^ 84646580022 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1100405540287) ^ 29740690278 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1100405540287) ^ 8658 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1171167993143 : Nat.Prime 1171167993143 := by
  apply lucas_primality 1171167993143 (5 : ZMod 1171167993143)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (2698543763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (2698543763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171167993143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_2698543763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1171167993143) ^ 585583996571 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171167993143) ^ 167309713306 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171167993143) ^ 37779612682 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171167993143) ^ 434 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1296047115893 : Nat.Prime 1296047115893 := by
  apply lucas_primality 1296047115893 (2 : ZMod 1296047115893)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 2), (612498637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 2), (612498637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1296047115893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_612498637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1296047115893) ^ 648023557946 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296047115893) ^ 56349874604 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1296047115893) ^ 2116 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1330619392903 : Nat.Prime 1330619392903 := by
  apply lucas_primality 1330619392903 (3 : ZMod 1330619392903)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1051, 1), (2281, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1051, 1), (2281, 1), (92507, 1)] : List FactorBlock).map factorBlockValue).prod) = 1330619392903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_1051
      · exact prime_oneHundredThirtyOneDY_2281
      · exact prime_oneHundredThirtyOneDY_92507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1330619392903) ^ 665309696451 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1330619392903) ^ 443539797634 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1330619392903) ^ 1266050802 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1330619392903) ^ 583349142 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1330619392903) ^ 14383986 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1435855587641 : Nat.Prime 1435855587641 := by
  apply lucas_primality 1435855587641 (3 : ZMod 1435855587641)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (137, 1), (262017443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (137, 1), (262017443, 1)] : List FactorBlock).map factorBlockValue).prod) = 1435855587641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_137
      · exact prime_oneHundredThirtyOneDY_262017443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1435855587641) ^ 717927793820 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1435855587641) ^ 287171117528 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1435855587641) ^ 10480697720 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 1435855587641) ^ 5480 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1987059294019 : Nat.Prime 1987059294019 := by
  apply lucas_primality 1987059294019 (10 : ZMod 1987059294019)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (1071768767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (1071768767, 1)] : List FactorBlock).map factorBlockValue).prod) = 1987059294019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_1071768767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 1987059294019) ^ 993529647009 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1987059294019) ^ 662353098006 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1987059294019) ^ 19291837806 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1987059294019) ^ 1854 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2196712776227 : Nat.Prime 2196712776227 := by
  apply lucas_primality 2196712776227 (2 : ZMod 2196712776227)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1098356388113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1098356388113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2196712776227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_1098356388113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2196712776227) ^ 1098356388113 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2196712776227) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4517028182629 : Nat.Prime 4517028182629 := by
  apply lucas_primality 4517028182629 (2 : ZMod 4517028182629)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (13, 2), (67, 1), (79, 1), (140269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (13, 2), (67, 1), (79, 1), (140269, 1)] : List FactorBlock).map factorBlockValue).prod) = 4517028182629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_67
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_140269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4517028182629) ^ 2258514091314 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4517028182629) ^ 1505676060876 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4517028182629) ^ 347463706356 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4517028182629) ^ 67418331084 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4517028182629) ^ 57177571932 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4517028182629) ^ 32202612 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5193896333209 : Nat.Prime 5193896333209 := by
  apply lucas_primality 5193896333209 (7 : ZMod 5193896333209)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (61, 1), (322522127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (61, 1), (322522127, 1)] : List FactorBlock).map factorBlockValue).prod) = 5193896333209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_61
      · exact prime_oneHundredThirtyOneDY_322522127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5193896333209) ^ 2596948166604 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 5193896333209) ^ 1731298777736 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 5193896333209) ^ 472172393928 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 5193896333209) ^ 85145841528 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 5193896333209) ^ 16104 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5447686565803 : Nat.Prime 5447686565803 := by
  apply lucas_primality 5447686565803 (3 : ZMod 5447686565803)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (293, 1), (238369063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (293, 1), (238369063, 1)] : List FactorBlock).map factorBlockValue).prod) = 5447686565803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_293
      · exact prime_oneHundredThirtyOneDY_238369063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5447686565803) ^ 2723843282901 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5447686565803) ^ 1815895521934 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5447686565803) ^ 419052812754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5447686565803) ^ 18592786914 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5447686565803) ^ 22854 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5476990925767 : Nat.Prime 5476990925767 := by
  apply lucas_primality 5476990925767 (5 : ZMod 5476990925767)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (15471725779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (15471725779, 1)] : List FactorBlock).map factorBlockValue).prod) = 5476990925767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_15471725779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5476990925767) ^ 2738495462883 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5476990925767) ^ 1825663641922 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5476990925767) ^ 92830354674 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 5476990925767) ^ 354 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_6472644906461 : Nat.Prime 6472644906461 := by
  apply lucas_primality 6472644906461 (3 : ZMod 6472644906461)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (2864002171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (2864002171, 1)] : List FactorBlock).map factorBlockValue).prod) = 6472644906461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_113
      · exact prime_oneHundredThirtyOneDY_2864002171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6472644906461) ^ 3236322453230 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472644906461) ^ 1294528981292 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472644906461) ^ 57280043420 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6472644906461) ^ 2260 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7549292142089 : Nat.Prime 7549292142089 := by
  apply lucas_primality 7549292142089 (3 : ZMod 7549292142089)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (15569, 1), (60611569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (15569, 1), (60611569, 1)] : List FactorBlock).map factorBlockValue).prod) = 7549292142089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_15569
      · exact prime_oneHundredThirtyOneDY_60611569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7549292142089) ^ 3774646071044 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7549292142089) ^ 484892552 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7549292142089) ^ 124552 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_8133518360707 : Nat.Prime 8133518360707 := by
  apply lucas_primality 8133518360707 (2 : ZMod 8133518360707)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1009, 1), (1343494939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1009, 1), (1343494939, 1)] : List FactorBlock).map factorBlockValue).prod) = 8133518360707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_1009
      · exact prime_oneHundredThirtyOneDY_1343494939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8133518360707) ^ 4066759180353 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8133518360707) ^ 2711172786902 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8133518360707) ^ 8060969634 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8133518360707) ^ 6054 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9572918156687 : Nat.Prime 9572918156687 := by
  apply lucas_primality 9572918156687 (5 : ZMod 9572918156687)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (157, 1), (1531, 1), (642359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (157, 1), (1531, 1), (642359, 1)] : List FactorBlock).map factorBlockValue).prod) = 9572918156687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_157
      · exact prime_oneHundredThirtyOneDY_1531
      · exact prime_oneHundredThirtyOneDY_642359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9572918156687) ^ 4786459078343 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9572918156687) ^ 308803811506 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9572918156687) ^ 60974000998 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9572918156687) ^ 6252722506 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9572918156687) ^ 14902754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9674534856313 : Nat.Prime 9674534856313 := by
  apply lucas_primality 9674534856313 (5 : ZMod 9674534856313)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (73, 1), (1840664927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (73, 1), (1840664927, 1)] : List FactorBlock).map factorBlockValue).prod) = 9674534856313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_73
      · exact prime_oneHundredThirtyOneDY_1840664927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 9674534856313) ^ 4837267428156 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9674534856313) ^ 3224844952104 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9674534856313) ^ 132527874744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9674534856313) ^ 5256 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_11370814037111 : Nat.Prime 11370814037111 := by
  apply lucas_primality 11370814037111 (7 : ZMod 11370814037111)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (877, 1), (200117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (877, 1), (200117, 1)] : List FactorBlock).map factorBlockValue).prod) = 11370814037111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_877
      · exact prime_oneHundredThirtyOneDY_200117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11370814037111) ^ 5685407018555 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 2274162807422 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 1033710367010 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 598463896690 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 366800452810 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 12965580430 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 11370814037111) ^ 56820830 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_13634203611571 : Nat.Prime 13634203611571 := by
  apply lucas_primality 13634203611571 (7 : ZMod 13634203611571)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (2251, 1), (11261, 1), (17929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (2251, 1), (11261, 1), (17929, 1)] : List FactorBlock).map factorBlockValue).prod) = 13634203611571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_2251
      · exact prime_oneHundredThirtyOneDY_11261
      · exact prime_oneHundredThirtyOneDY_17929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 13634203611571) ^ 6817101805785 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 13634203611571) ^ 4544734537190 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 13634203611571) ^ 2726840722314 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 13634203611571) ^ 6056954070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 13634203611571) ^ 1210745370 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 13634203611571) ^ 760455330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_14439449377921 : Nat.Prime 14439449377921 := by
  apply lucas_primality 14439449377921 (22 : ZMod 14439449377921)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 1), (7, 1), (421, 1), (2551933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 1), (7, 1), (421, 1), (2551933, 1)] : List FactorBlock).map factorBlockValue).prod) = 14439449377921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_421
      · exact prime_oneHundredThirtyOneDY_2551933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (22 : ZMod 14439449377921) ^ 7219724688960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 14439449377921) ^ 4813149792640 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 14439449377921) ^ 2887889875584 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 14439449377921) ^ 2062778482560 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 14439449377921) ^ 34297979520 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (22 : ZMod 14439449377921) ^ 5658240 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_20424975333397 : Nat.Prime 20424975333397 := by
  apply lucas_primality 20424975333397 (7 : ZMod 20424975333397)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (344153, 1), (4945711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (344153, 1), (4945711, 1)] : List FactorBlock).map factorBlockValue).prod) = 20424975333397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_344153
      · exact prime_oneHundredThirtyOneDY_4945711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 20424975333397) ^ 10212487666698 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20424975333397) ^ 6808325111132 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20424975333397) ^ 59348532 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 20424975333397) ^ 4129836 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_24730037977327 : Nat.Prime 24730037977327 := by
  apply lucas_primality 24730037977327 (5 : ZMod 24730037977327)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (503, 1), (8867, 1), (84011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (503, 1), (8867, 1), (84011, 1)] : List FactorBlock).map factorBlockValue).prod) = 24730037977327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_503
      · exact prime_oneHundredThirtyOneDY_8867
      · exact prime_oneHundredThirtyOneDY_84011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24730037977327) ^ 12365018988663 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24730037977327) ^ 8243345992442 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24730037977327) ^ 2248185270666 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24730037977327) ^ 49165085442 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24730037977327) ^ 2788997178 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 24730037977327) ^ 294366666 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_25973041894399 : Nat.Prime 25973041894399 := by
  apply lucas_primality 25973041894399 (6 : ZMod 25973041894399)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (109, 1), (2857, 1), (125231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (109, 1), (2857, 1), (125231, 1)] : List FactorBlock).map factorBlockValue).prod) = 25973041894399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_109
      · exact prime_oneHundredThirtyOneDY_2857
      · exact prime_oneHundredThirtyOneDY_125231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 25973041894399) ^ 12986520947199 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25973041894399) ^ 8657680631466 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25973041894399) ^ 701974105254 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25973041894399) ^ 238284788022 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25973041894399) ^ 9091019214 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 25973041894399) ^ 207401058 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_30680576811653 : Nat.Prime 30680576811653 := by
  apply lucas_primality 30680576811653 (2 : ZMod 30680576811653)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7459, 1), (1028307307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7459, 1), (1028307307, 1)] : List FactorBlock).map factorBlockValue).prod) = 30680576811653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7459
      · exact prime_oneHundredThirtyOneDY_1028307307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30680576811653) ^ 15340288405826 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30680576811653) ^ 4113229228 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30680576811653) ^ 29836 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_30783652644611 : Nat.Prime 30783652644611 := by
  apply lucas_primality 30783652644611 (2 : ZMod 30783652644611)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 1), (541, 1), (138783881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 1), (541, 1), (138783881, 1)] : List FactorBlock).map factorBlockValue).prod) = 30783652644611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_541
      · exact prime_oneHundredThirtyOneDY_138783881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30783652644611) ^ 15391826322305 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30783652644611) ^ 6156730528922 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30783652644611) ^ 750820796210 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30783652644611) ^ 56901391210 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 30783652644611) ^ 221810 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_31100264197753 : Nat.Prime 31100264197753 := by
  apply lucas_primality 31100264197753 (15 : ZMod 31100264197753)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (68202333767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (68202333767, 1)] : List FactorBlock).map factorBlockValue).prod) = 31100264197753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_68202333767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 31100264197753) ^ 15550132098876 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 31100264197753) ^ 10366754732584 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 31100264197753) ^ 1636856010408 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 31100264197753) ^ 456 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_32177292986549 : Nat.Prime 32177292986549 := by
  apply lucas_primality 32177292986549 (2 : ZMod 32177292986549)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (2357, 1), (5857, 1), (15749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (2357, 1), (5857, 1), (15749, 1)] : List FactorBlock).map factorBlockValue).prod) = 32177292986549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_2357
      · exact prime_oneHundredThirtyOneDY_5857
      · exact prime_oneHundredThirtyOneDY_15749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 32177292986549) ^ 16088646493274 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32177292986549) ^ 869656567204 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32177292986549) ^ 13651800164 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32177292986549) ^ 5493818164 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32177292986549) ^ 2043132452 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_33678089409121 : Nat.Prime 33678089409121 := by
  apply lucas_primality 33678089409121 (28 : ZMod 33678089409121)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (13, 1), (5623, 1), (959831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (13, 1), (5623, 1), (959831, 1)] : List FactorBlock).map factorBlockValue).prod) = 33678089409121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_5623
      · exact prime_oneHundredThirtyOneDY_959831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (28 : ZMod 33678089409121) ^ 16839044704560 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (28 : ZMod 33678089409121) ^ 11226029803040 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (28 : ZMod 33678089409121) ^ 6735617881824 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (28 : ZMod 33678089409121) ^ 2590622262240 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (28 : ZMod 33678089409121) ^ 5989345440 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (28 : ZMod 33678089409121) ^ 35087520 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_35321769486343 : Nat.Prime 35321769486343 := by
  apply lucas_primality 35321769486343 (3 : ZMod 35321769486343)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (143137, 1), (13709387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (143137, 1), (13709387, 1)] : List FactorBlock).map factorBlockValue).prod) = 35321769486343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_143137
      · exact prime_oneHundredThirtyOneDY_13709387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 35321769486343) ^ 17660884743171 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35321769486343) ^ 11773923162114 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35321769486343) ^ 246768966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35321769486343) ^ 2576466 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_49031970605467 : Nat.Prime 49031970605467 := by
  apply lucas_primality 49031970605467 (2 : ZMod 49031970605467)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (709, 1), (977, 1), (176081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (709, 1), (977, 1), (176081, 1)] : List FactorBlock).map factorBlockValue).prod) = 49031970605467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_67
      · exact prime_oneHundredThirtyOneDY_709
      · exact prime_oneHundredThirtyOneDY_977
      · exact prime_oneHundredThirtyOneDY_176081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 49031970605467) ^ 24515985302733 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49031970605467) ^ 16343990201822 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49031970605467) ^ 731820456798 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49031970605467) ^ 69156517074 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49031970605467) ^ 50186254458 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 49031970605467) ^ 278462586 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_56442911347373 : Nat.Prime 56442911347373 := by
  apply lucas_primality 56442911347373 (2 : ZMod 56442911347373)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (173, 1), (181, 1), (40966801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (173, 1), (181, 1), (40966801, 1)] : List FactorBlock).map factorBlockValue).prod) = 56442911347373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_173
      · exact prime_oneHundredThirtyOneDY_181
      · exact prime_oneHundredThirtyOneDY_40966801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56442911347373) ^ 28221455673686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56442911347373) ^ 5131173758852 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56442911347373) ^ 326259603164 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56442911347373) ^ 311839289212 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 56442911347373) ^ 1377772 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_61361153623307 : Nat.Prime 61361153623307 := by
  apply lucas_primality 61361153623307 (2 : ZMod 61361153623307)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (30680576811653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (30680576811653, 1)] : List FactorBlock).map factorBlockValue).prod) = 61361153623307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_30680576811653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 61361153623307) ^ 30680576811653 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 61361153623307) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_82659071302957 : Nat.Prime 82659071302957 := by
  apply lucas_primality 82659071302957 (6 : ZMod 82659071302957)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (107719, 1), (21315509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (107719, 1), (21315509, 1)] : List FactorBlock).map factorBlockValue).prod) = 82659071302957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_107719
      · exact prime_oneHundredThirtyOneDY_21315509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 82659071302957) ^ 41329535651478 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82659071302957) ^ 27553023767652 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82659071302957) ^ 767358324 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82659071302957) ^ 3877884 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_99868254680009 : Nat.Prime 99868254680009 := by
  apply lucas_primality 99868254680009 (3 : ZMod 99868254680009)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (59, 1), (211585285339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (59, 1), (211585285339, 1)] : List FactorBlock).map factorBlockValue).prod) = 99868254680009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_211585285339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 99868254680009) ^ 49934127340004 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 99868254680009) ^ 1692682282712 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 99868254680009) ^ 472 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_106878251484581 : Nat.Prime 106878251484581 := by
  apply lucas_primality 106878251484581 (2 : ZMod 106878251484581)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (366139, 1), (14595311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (366139, 1), (14595311, 1)] : List FactorBlock).map factorBlockValue).prod) = 106878251484581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_366139
      · exact prime_oneHundredThirtyOneDY_14595311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 106878251484581) ^ 53439125742290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106878251484581) ^ 21375650296916 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106878251484581) ^ 291906220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106878251484581) ^ 7322780 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_108821547845827 : Nat.Prime 108821547845827 := by
  apply lucas_primality 108821547845827 (2 : ZMod 108821547845827)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (199, 1), (91140324829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (199, 1), (91140324829, 1)] : List FactorBlock).map factorBlockValue).prod) = 108821547845827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_199
      · exact prime_oneHundredThirtyOneDY_91140324829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 108821547845827) ^ 54410773922913 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108821547845827) ^ 36273849281942 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108821547845827) ^ 546841948974 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 108821547845827) ^ 1194 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_112316893058863 : Nat.Prime 112316893058863 := by
  apply lucas_primality 112316893058863 (10 : ZMod 112316893058863)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (211, 1), (271, 1), (1229, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (211, 1), (271, 1), (1229, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 112316893058863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_211
      · exact prime_oneHundredThirtyOneDY_271
      · exact prime_oneHundredThirtyOneDY_1229
      · exact prime_oneHundredThirtyOneDY_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 112316893058863) ^ 56158446529431 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 37438964352954 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 6606876062286 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 532307550042 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 414453479922 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 91388847078 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 112316893058863) ^ 64512862182 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_148231820665969 : Nat.Prime 148231820665969 := by
  apply lucas_primality 148231820665969 (7 : ZMod 148231820665969)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (17, 1), (16433, 1), (850337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (17, 1), (16433, 1), (850337, 1)] : List FactorBlock).map factorBlockValue).prod) = 148231820665969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_16433
      · exact prime_oneHundredThirtyOneDY_850337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 148231820665969) ^ 74115910332984 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 148231820665969) ^ 49410606888656 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 148231820665969) ^ 11402447743536 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 148231820665969) ^ 8719518862704 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 148231820665969) ^ 9020374896 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 148231820665969) ^ 174321264 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_151754627593039 : Nat.Prime 151754627593039 := by
  apply lucas_primality 151754627593039 (3 : ZMod 151754627593039)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (53, 1), (1423, 1), (8179487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (53, 1), (1423, 1), (8179487, 1)] : List FactorBlock).map factorBlockValue).prod) = 151754627593039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_53
      · exact prime_oneHundredThirtyOneDY_1423
      · exact prime_oneHundredThirtyOneDY_8179487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 151754627593039) ^ 75877313796519 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 151754627593039) ^ 50584875864346 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 151754627593039) ^ 3701332380318 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 151754627593039) ^ 2863294860246 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 151754627593039) ^ 106644151506 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 151754627593039) ^ 18553074 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_159614138877877 : Nat.Prime 159614138877877 := by
  apply lucas_primality 159614138877877 (2 : ZMod 159614138877877)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (37, 1), (2393, 1), (50075401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (37, 1), (2393, 1), (50075401, 1)] : List FactorBlock).map factorBlockValue).prod) = 159614138877877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_2393
      · exact prime_oneHundredThirtyOneDY_50075401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159614138877877) ^ 79807069438938 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 159614138877877) ^ 53204712959292 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 159614138877877) ^ 4313895645348 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 159614138877877) ^ 66700434132 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 159614138877877) ^ 3187476 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_199967702415493 : Nat.Prime 199967702415493 := by
  apply lucas_primality 199967702415493 (6 : ZMod 199967702415493)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (37, 1), (59, 2), (89, 1), (132157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (37, 1), (59, 2), (89, 1), (132157, 1)] : List FactorBlock).map factorBlockValue).prod) = 199967702415493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_89
      · exact prime_oneHundredThirtyOneDY_132157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 199967702415493) ^ 99983851207746 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 66655900805164 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 18178882037772 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 5404532497716 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 3389283091788 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 2246828117028 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 199967702415493) ^ 1513107156 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_204114977281357 : Nat.Prime 204114977281357 := by
  apply lucas_primality 204114977281357 (2 : ZMod 204114977281357)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (895241128427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (895241128427, 1)] : List FactorBlock).map factorBlockValue).prod) = 204114977281357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_895241128427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 204114977281357) ^ 102057488640678 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 204114977281357) ^ 68038325760452 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 204114977281357) ^ 10742893541124 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 204114977281357) ^ 228 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_256765463863471 : Nat.Prime 256765463863471 := by
  apply lucas_primality 256765463863471 (6 : ZMod 256765463863471)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (43, 1), (647, 1), (823, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (43, 1), (647, 1), (823, 1), (124601, 1)] : List FactorBlock).map factorBlockValue).prod) = 256765463863471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_43
      · exact prime_oneHundredThirtyOneDY_647
      · exact prime_oneHundredThirtyOneDY_823
      · exact prime_oneHundredThirtyOneDY_124601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 256765463863471) ^ 128382731931735 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 85588487954490 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 51353092772694 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 5971289857290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 396855431010 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 311987197890 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 256765463863471) ^ 2060701470 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_816049246311823 : Nat.Prime 816049246311823 := by
  apply lucas_primality 816049246311823 (5 : ZMod 816049246311823)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17107, 1), (7950441791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17107, 1), (7950441791, 1)] : List FactorBlock).map factorBlockValue).prod) = 816049246311823 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17107
      · exact prime_oneHundredThirtyOneDY_7950441791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 816049246311823) ^ 408024623155911 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 816049246311823) ^ 272016415437274 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 816049246311823) ^ 47702650746 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 816049246311823) ^ 102642 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1123912206566243 : Nat.Prime 1123912206566243 := by
  apply lucas_primality 1123912206566243 (2 : ZMod 1123912206566243)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (1291, 1), (1373146543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (1291, 1), (1373146543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1123912206566243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_317
      · exact prime_oneHundredThirtyOneDY_1291
      · exact prime_oneHundredThirtyOneDY_1373146543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1123912206566243) ^ 561956103283121 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123912206566243) ^ 3545464374026 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123912206566243) ^ 870574908262 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1123912206566243) ^ 818494 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1433063133352517 : Nat.Prime 1433063133352517 := by
  apply lucas_primality 1433063133352517 (2 : ZMod 1433063133352517)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (144497, 1), (85496533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (144497, 1), (85496533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1433063133352517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_144497
      · exact prime_oneHundredThirtyOneDY_85496533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1433063133352517) ^ 716531566676258 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433063133352517) ^ 49415970115604 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433063133352517) ^ 9917597828 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1433063133352517) ^ 16761652 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1606156121713711 : Nat.Prime 1606156121713711 := by
  apply lucas_primality 1606156121713711 (6 : ZMod 1606156121713711)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (367, 1), (20840224753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (367, 1), (20840224753, 1)] : List FactorBlock).map factorBlockValue).prod) = 1606156121713711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_367
      · exact prime_oneHundredThirtyOneDY_20840224753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1606156121713711) ^ 803078060856855 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1606156121713711) ^ 535385373904570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1606156121713711) ^ 321231224342742 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1606156121713711) ^ 229450874530530 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1606156121713711) ^ 4376447198130 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1606156121713711) ^ 77070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1885183110173837 : Nat.Prime 1885183110173837 := by
  apply lucas_primality 1885183110173837 (2 : ZMod 1885183110173837)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (780853, 1), (4988143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (780853, 1), (4988143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1885183110173837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_780853
      · exact prime_oneHundredThirtyOneDY_4988143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1885183110173837) ^ 942591555086918 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1885183110173837) ^ 171380282743076 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1885183110173837) ^ 2414261212 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1885183110173837) ^ 377932852 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2528731931579527 : Nat.Prime 2528731931579527 := by
  apply lucas_primality 2528731931579527 (5 : ZMod 2528731931579527)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (383, 1), (1100405540287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (383, 1), (1100405540287, 1)] : List FactorBlock).map factorBlockValue).prod) = 2528731931579527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_383
      · exact prime_oneHundredThirtyOneDY_1100405540287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2528731931579527) ^ 1264365965789763 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2528731931579527) ^ 842910643859842 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2528731931579527) ^ 6602433241722 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2528731931579527) ^ 2298 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_3237504589125923 : Nat.Prime 3237504589125923 := by
  apply lucas_primality 3237504589125923 (2 : ZMod 3237504589125923)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (191, 1), (208367, 1), (373157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (191, 1), (208367, 1), (373157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3237504589125923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_109
      · exact prime_oneHundredThirtyOneDY_191
      · exact prime_oneHundredThirtyOneDY_208367
      · exact prime_oneHundredThirtyOneDY_373157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3237504589125923) ^ 1618752294562961 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3237504589125923) ^ 29701876964458 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3237504589125923) ^ 16950285806942 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3237504589125923) ^ 15537511166 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3237504589125923) ^ 8675985146 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4726044150731051 : Nat.Prime 4726044150731051 := by
  apply lucas_primality 4726044150731051 (2 : ZMod 4726044150731051)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (19, 1), (25031, 1), (28392127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (19, 1), (25031, 1), (28392127, 1)] : List FactorBlock).map factorBlockValue).prod) = 4726044150731051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_25031
      · exact prime_oneHundredThirtyOneDY_28392127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4726044150731051) ^ 2363022075365525 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4726044150731051) ^ 945208830146210 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4726044150731051) ^ 675149164390150 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4726044150731051) ^ 248739165827950 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4726044150731051) ^ 188807644550 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4726044150731051) ^ 166456150 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5292180373423913 : Nat.Prime 5292180373423913 := by
  apply lucas_primality 5292180373423913 (3 : ZMod 5292180373423913)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (1571, 1), (14520128771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (1571, 1), (14520128771, 1)] : List FactorBlock).map factorBlockValue).prod) = 5292180373423913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_1571
      · exact prime_oneHundredThirtyOneDY_14520128771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5292180373423913) ^ 2646090186711956 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5292180373423913) ^ 182488978393928 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5292180373423913) ^ 3368669874872 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 5292180373423913) ^ 364472 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_5707730577142549 : Nat.Prime 5707730577142549 := by
  apply lucas_primality 5707730577142549 (2 : ZMod 5707730577142549)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (33811, 1), (4689245263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (33811, 1), (4689245263, 1)] : List FactorBlock).map factorBlockValue).prod) = 5707730577142549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_33811
      · exact prime_oneHundredThirtyOneDY_4689245263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5707730577142549) ^ 2853865288571274 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5707730577142549) ^ 1902576859047516 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5707730577142549) ^ 168812829468 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5707730577142549) ^ 1217196 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_6475009178251847 : Nat.Prime 6475009178251847 := by
  apply lucas_primality 6475009178251847 (5 : ZMod 6475009178251847)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3237504589125923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3237504589125923, 1)] : List FactorBlock).map factorBlockValue).prod) = 6475009178251847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3237504589125923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 6475009178251847) ^ 3237504589125923 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6475009178251847) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7372062866764987 : Nat.Prime 7372062866764987 := by
  apply lucas_primality 7372062866764987 (2 : ZMod 7372062866764987)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (251, 1), (13241, 1), (28438057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (251, 1), (13241, 1), (28438057, 1)] : List FactorBlock).map factorBlockValue).prod) = 7372062866764987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_251
      · exact prime_oneHundredThirtyOneDY_13241
      · exact prime_oneHundredThirtyOneDY_28438057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7372062866764987) ^ 3686031433382493 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7372062866764987) ^ 2457354288921662 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7372062866764987) ^ 567081758981922 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7372062866764987) ^ 29370768393486 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7372062866764987) ^ 556760279946 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7372062866764987) ^ 259232298 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_9820577400857933 : Nat.Prime 9820577400857933 := by
  apply lucas_primality 9820577400857933 (2 : ZMod 9820577400857933)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (2477, 1), (16248796139, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (2477, 1), (16248796139, 1)] : List FactorBlock).map factorBlockValue).prod) = 9820577400857933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_61
      · exact prime_oneHundredThirtyOneDY_2477
      · exact prime_oneHundredThirtyOneDY_16248796139
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9820577400857933) ^ 4910288700428966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9820577400857933) ^ 160993072145212 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9820577400857933) ^ 3964706257916 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9820577400857933) ^ 604388 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_10025591520348737 : Nat.Prime 10025591520348737 := by
  apply lucas_primality 10025591520348737 (3 : ZMod 10025591520348737)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (30211, 1), (5185193059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (30211, 1), (5185193059, 1)] : List FactorBlock).map factorBlockValue).prod) = 10025591520348737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_30211
      · exact prime_oneHundredThirtyOneDY_5185193059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10025591520348737) ^ 5012795760174368 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10025591520348737) ^ 331852355776 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10025591520348737) ^ 1933504 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_11432846756058911 : Nat.Prime 11432846756058911 := by
  apply lucas_primality 11432846756058911 (14 : ZMod 11432846756058911)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (13, 1), (17, 1), (281, 1), (2630012113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (13, 1), (17, 1), (281, 1), (2630012113, 1)] : List FactorBlock).map factorBlockValue).prod) = 11432846756058911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_281
      · exact prime_oneHundredThirtyOneDY_2630012113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 11432846756058911) ^ 5716423378029455 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 2286569351211782 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 1633263822294130 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 879449750466070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 672520397415230 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 40686287388110 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 11432846756058911) ^ 4347070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_11461158628235761 : Nat.Prime 11461158628235761 := by
  apply lucas_primality 11461158628235761 (23 : ZMod 11461158628235761)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (79, 1), (604491488831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (79, 1), (604491488831, 1)] : List FactorBlock).map factorBlockValue).prod) = 11461158628235761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_604491488831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 11461158628235761) ^ 5730579314117880 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (23 : ZMod 11461158628235761) ^ 3820386209411920 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (23 : ZMod 11461158628235761) ^ 2292231725647152 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (23 : ZMod 11461158628235761) ^ 145077957319440 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (23 : ZMod 11461158628235761) ^ 18960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_15678844077625319 : Nat.Prime 15678844077625319 := by
  apply lucas_primality 15678844077625319 (13 : ZMod 15678844077625319)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (317, 1), (24730037977327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (317, 1), (24730037977327, 1)] : List FactorBlock).map factorBlockValue).prod) = 15678844077625319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_317
      · exact prime_oneHundredThirtyOneDY_24730037977327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 15678844077625319) ^ 7839422038812659 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 15678844077625319) ^ 49460075954654 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 15678844077625319) ^ 634 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_18221916511256687 : Nat.Prime 18221916511256687 := by
  apply lucas_primality 18221916511256687 (5 : ZMod 18221916511256687)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (808559, 1), (11268142777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (808559, 1), (11268142777, 1)] : List FactorBlock).map factorBlockValue).prod) = 18221916511256687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_808559
      · exact prime_oneHundredThirtyOneDY_11268142777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18221916511256687) ^ 9110958255628343 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 18221916511256687) ^ 22536285554 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 18221916511256687) ^ 1617118 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_18654893502634267 : Nat.Prime 18654893502634267 := by
  apply lucas_primality 18654893502634267 (2 : ZMod 18654893502634267)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (101, 1), (30783652644611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (101, 1), (30783652644611, 1)] : List FactorBlock).map factorBlockValue).prod) = 18654893502634267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_101
      · exact prime_oneHundredThirtyOneDY_30783652644611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 18654893502634267) ^ 9327446751317133 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18654893502634267) ^ 6218297834211422 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18654893502634267) ^ 184701915867666 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 18654893502634267) ^ 606 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_19303316843763893 : Nat.Prime 19303316843763893 := by
  apply lucas_primality 19303316843763893 (2 : ZMod 19303316843763893)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (4649, 1), (9523265753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (4649, 1), (9523265753, 1)] : List FactorBlock).map factorBlockValue).prod) = 19303316843763893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_109
      · exact prime_oneHundredThirtyOneDY_4649
      · exact prime_oneHundredThirtyOneDY_9523265753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19303316843763893) ^ 9651658421881946 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19303316843763893) ^ 177094649942788 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19303316843763893) ^ 4152143868308 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 19303316843763893) ^ 2026964 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_19522854821151991 : Nat.Prime 19522854821151991 := by
  apply lucas_primality 19522854821151991 (12 : ZMod 19522854821151991)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (107, 1), (14207, 1), (1853207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (11, 1), (107, 1), (14207, 1), (1853207, 1)] : List FactorBlock).map factorBlockValue).prod) = 19522854821151991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_107
      · exact prime_oneHundredThirtyOneDY_14207
      · exact prime_oneHundredThirtyOneDY_1853207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 19522854821151991) ^ 9761427410575995 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 6507618273717330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 3904570964230398 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 2788979260164570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 1774804983741090 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 182456587113570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 1374171522570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (12 : ZMod 19522854821151991) ^ 10534632570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_20465943002856259 : Nat.Prime 20465943002856259 := by
  apply lucas_primality 20465943002856259 (2 : ZMod 20465943002856259)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (103, 1), (106921, 1), (309727861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (103, 1), (106921, 1), (309727861, 1)] : List FactorBlock).map factorBlockValue).prod) = 20465943002856259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_103
      · exact prime_oneHundredThirtyOneDY_106921
      · exact prime_oneHundredThirtyOneDY_309727861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20465943002856259) ^ 10232971501428129 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20465943002856259) ^ 6821981000952086 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20465943002856259) ^ 198698475755886 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20465943002856259) ^ 191411818098 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20465943002856259) ^ 66077178 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_35612492275348423 : Nat.Prime 35612492275348423 := by
  apply lucas_primality 35612492275348423 (3 : ZMod 35612492275348423)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (131, 1), (6472644906461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (131, 1), (6472644906461, 1)] : List FactorBlock).map factorBlockValue).prod) = 35612492275348423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_131
      · exact prime_oneHundredThirtyOneDY_6472644906461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35612492275348423) ^ 17806246137674211 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35612492275348423) ^ 11870830758449474 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35612492275348423) ^ 5087498896478346 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35612492275348423) ^ 271851086071362 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 35612492275348423) ^ 5502 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_62101743154562399 : Nat.Prime 62101743154562399 := by
  apply lucas_primality 62101743154562399 (7 : ZMod 62101743154562399)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (281, 1), (5651, 1), (15581, 1), (179287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (281, 1), (5651, 1), (15581, 1), (179287, 1)] : List FactorBlock).map factorBlockValue).prod) = 62101743154562399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_281
      · exact prime_oneHundredThirtyOneDY_5651
      · exact prime_oneHundredThirtyOneDY_15581
      · exact prime_oneHundredThirtyOneDY_179287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 62101743154562399) ^ 31050871577281199 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 62101743154562399) ^ 8871677593508914 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 62101743154562399) ^ 221002644678158 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 62101743154562399) ^ 10989513918698 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 62101743154562399) ^ 3985735392758 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 62101743154562399) ^ 346381740754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_93186287800952263 : Nat.Prime 93186287800952263 := by
  apply lucas_primality 93186287800952263 (5 : ZMod 93186287800952263)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (17, 1), (47, 1), (109961, 1), (3607607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (17, 1), (47, 1), (109961, 1), (3607607, 1)] : List FactorBlock).map factorBlockValue).prod) = 93186287800952263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_47
      · exact prime_oneHundredThirtyOneDY_109961
      · exact prime_oneHundredThirtyOneDY_3607607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 93186287800952263) ^ 46593143900476131 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 31062095933650754 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 13312326828707466 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 5481546341232486 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 1982686974488346 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 847448529942 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 93186287800952263) ^ 25830498666 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_106090896923230187 : Nat.Prime 106090896923230187 := by
  apply lucas_primality 106090896923230187 (2 : ZMod 106090896923230187)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (53, 1), (229, 1), (397323349799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (53, 1), (229, 1), (397323349799, 1)] : List FactorBlock).map factorBlockValue).prod) = 106090896923230187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_53
      · exact prime_oneHundredThirtyOneDY_229
      · exact prime_oneHundredThirtyOneDY_397323349799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106090896923230187) ^ 53045448461615093 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106090896923230187) ^ 9644626993020926 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106090896923230187) ^ 2001715036287362 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106090896923230187) ^ 463279025865634 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 106090896923230187) ^ 267014 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_108955242046533067 : Nat.Prime 108955242046533067 := by
  apply lucas_primality 108955242046533067 (5 : ZMod 108955242046533067)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (555257, 1), (32704147823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (555257, 1), (32704147823, 1)] : List FactorBlock).map factorBlockValue).prod) = 108955242046533067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_555257
      · exact prime_oneHundredThirtyOneDY_32704147823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 108955242046533067) ^ 54477621023266533 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 108955242046533067) ^ 36318414015511022 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 108955242046533067) ^ 196224886938 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 108955242046533067) ^ 3331542 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_125570072697136079 : Nat.Prime 125570072697136079 := by
  apply lucas_primality 125570072697136079 (11 : ZMod 125570072697136079)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (5707730577142549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (5707730577142549, 1)] : List FactorBlock).map factorBlockValue).prod) = 125570072697136079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_5707730577142549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 125570072697136079) ^ 62785036348568039 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 125570072697136079) ^ 11415461154285098 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 125570072697136079) ^ 22 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_148305002971698091 : Nat.Prime 148305002971698091 := by
  apply lucas_primality 148305002971698091 (2 : ZMod 148305002971698091)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (67, 1), (1171167993143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (67, 1), (1171167993143, 1)] : List FactorBlock).map factorBlockValue).prod) = 148305002971698091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_67
      · exact prime_oneHundredThirtyOneDY_1171167993143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148305002971698091) ^ 74152501485849045 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148305002971698091) ^ 49435000990566030 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148305002971698091) ^ 29661000594339618 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148305002971698091) ^ 21186428995956870 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148305002971698091) ^ 2213507507040270 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148305002971698091) ^ 126630 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_152143442913768203 : Nat.Prime 152143442913768203 := by
  apply lucas_primality 152143442913768203 (2 : ZMod 152143442913768203)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (6899, 1), (848191169923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (6899, 1), (848191169923, 1)] : List FactorBlock).map factorBlockValue).prod) = 152143442913768203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_6899
      · exact prime_oneHundredThirtyOneDY_848191169923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 152143442913768203) ^ 76071721456884101 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 152143442913768203) ^ 11703341762597554 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 152143442913768203) ^ 22052970417998 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 152143442913768203) ^ 179374 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_158943238354202369 : Nat.Prime 158943238354202369 := by
  apply lucas_primality 158943238354202369 (3 : ZMod 158943238354202369)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (11, 1), (56442911347373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (11, 1), (56442911347373, 1)] : List FactorBlock).map factorBlockValue).prod) = 158943238354202369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_56442911347373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 158943238354202369) ^ 79471619177101184 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 158943238354202369) ^ 14449385304927488 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 158943238354202369) ^ 2816 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_186548935026342671 : Nat.Prime 186548935026342671 := by
  apply lucas_primality 186548935026342671 (19 : ZMod 186548935026342671)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18654893502634267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18654893502634267, 1)] : List FactorBlock).map factorBlockValue).prod) = 186548935026342671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_18654893502634267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 186548935026342671) ^ 93274467513171335 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (19 : ZMod 186548935026342671) ^ 37309787005268534 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (19 : ZMod 186548935026342671) ^ 10 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_217859376279492707 : Nat.Prime 217859376279492707 := by
  apply lucas_primality 217859376279492707 (2 : ZMod 217859376279492707)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (41, 1), (59, 1), (14503, 1), (282266839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (41, 1), (59, 1), (14503, 1), (282266839, 1)] : List FactorBlock).map factorBlockValue).prod) = 217859376279492707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_14503
      · exact prime_oneHundredThirtyOneDY_282266839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 217859376279492707) ^ 108929688139746353 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 217859376279492707) ^ 19805397843590246 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 217859376279492707) ^ 5313643323890066 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 217859376279492707) ^ 3692531801347334 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 217859376279492707) ^ 15021676637902 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 217859376279492707) ^ 771820654 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_236587782076245217 : Nat.Prime 236587782076245217 := by
  apply lucas_primality 236587782076245217 (11 : ZMod 236587782076245217)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (101, 1), (8133518360707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (101, 1), (8133518360707, 1)] : List FactorBlock).map factorBlockValue).prod) = 236587782076245217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_101
      · exact prime_oneHundredThirtyOneDY_8133518360707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 236587782076245217) ^ 118293891038122608 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 236587782076245217) ^ 78862594025415072 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 236587782076245217) ^ 2342453287883616 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (11 : ZMod 236587782076245217) ^ 29088 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_851871546730275581 : Nat.Prime 851871546730275581 := by
  apply lucas_primality 851871546730275581 (2 : ZMod 851871546730275581)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (241, 1), (3593, 1), (10303, 1), (4774261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (241, 1), (3593, 1), (10303, 1), (4774261, 1)] : List FactorBlock).map factorBlockValue).prod) = 851871546730275581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_241
      · exact prime_oneHundredThirtyOneDY_3593
      · exact prime_oneHundredThirtyOneDY_10303
      · exact prime_oneHundredThirtyOneDY_4774261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 851871546730275581) ^ 425935773365137790 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 851871546730275581) ^ 170374309346055116 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 851871546730275581) ^ 3534736708424380 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 851871546730275581) ^ 237091997420060 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 851871546730275581) ^ 82681893305860 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 851871546730275581) ^ 178430032780 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1154737205783515261 : Nat.Prime 1154737205783515261 := by
  apply lucas_primality 1154737205783515261 (6 : ZMod 1154737205783515261)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (41, 1), (292133, 1), (535606919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (41, 1), (292133, 1), (535606919, 1)] : List FactorBlock).map factorBlockValue).prod) = 1154737205783515261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_41
      · exact prime_oneHundredThirtyOneDY_292133
      · exact prime_oneHundredThirtyOneDY_535606919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1154737205783515261) ^ 577368602891757630 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1154737205783515261) ^ 384912401927838420 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1154737205783515261) ^ 230947441156703052 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1154737205783515261) ^ 28164322092280860 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1154737205783515261) ^ 3952779062220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1154737205783515261) ^ 2155941540 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1171028955262083727 : Nat.Prime 1171028955262083727 := by
  apply lucas_primality 1171028955262083727 (5 : ZMod 1171028955262083727)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 2), (37967, 1), (17787391267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 2), (37967, 1), (17787391267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1171028955262083727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_37967
      · exact prime_oneHundredThirtyOneDY_17787391267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1171028955262083727) ^ 585514477631041863 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171028955262083727) ^ 390342985087361242 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171028955262083727) ^ 68884056191887278 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171028955262083727) ^ 30843336456978 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1171028955262083727) ^ 65834778 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1276549268748683159 : Nat.Prime 1276549268748683159 := by
  apply lucas_primality 1276549268748683159 (17 : ZMod 1276549268748683159)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (22961, 1), (261631, 1), (106249669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (22961, 1), (261631, 1), (106249669, 1)] : List FactorBlock).map factorBlockValue).prod) = 1276549268748683159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_22961
      · exact prime_oneHundredThirtyOneDY_261631
      · exact prime_oneHundredThirtyOneDY_106249669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1276549268748683159) ^ 638274634374341579 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 1276549268748683159) ^ 55596414300278 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 1276549268748683159) ^ 4879197299818 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (17 : ZMod 1276549268748683159) ^ 12014618782 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1458891180555799163 : Nat.Prime 1458891180555799163 := by
  apply lucas_primality 1458891180555799163 (2 : ZMod 1458891180555799163)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (73, 1), (443, 1), (521, 1), (2546711047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (73, 1), (443, 1), (521, 1), (2546711047, 1)] : List FactorBlock).map factorBlockValue).prod) = 1458891180555799163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_73
      · exact prime_oneHundredThirtyOneDY_443
      · exact prime_oneHundredThirtyOneDY_521
      · exact prime_oneHundredThirtyOneDY_2546711047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1458891180555799163) ^ 729445590277899581 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458891180555799163) ^ 85817128267988186 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458891180555799163) ^ 19984810692545194 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458891180555799163) ^ 3293208082518734 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458891180555799163) ^ 2800175010663722 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1458891180555799163) ^ 572853046 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2553098537497366319 : Nat.Prime 2553098537497366319 := by
  apply lucas_primality 2553098537497366319 (13 : ZMod 2553098537497366319)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1276549268748683159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1276549268748683159, 1)] : List FactorBlock).map factorBlockValue).prod) = 2553098537497366319 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_1276549268748683159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 2553098537497366319) ^ 1276549268748683159 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 2553098537497366319) ^ 2 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2860395245590249469 : Nat.Prime 2860395245590249469 := by
  apply lucas_primality 2860395245590249469 (2 : ZMod 2860395245590249469)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (223, 1), (20424975333397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (223, 1), (20424975333397, 1)] : List FactorBlock).map factorBlockValue).prod) = 2860395245590249469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_157
      · exact prime_oneHundredThirtyOneDY_223
      · exact prime_oneHundredThirtyOneDY_20424975333397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2860395245590249469) ^ 1430197622795124734 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860395245590249469) ^ 18219077997390124 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860395245590249469) ^ 12826884509373316 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2860395245590249469) ^ 140044 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_6425956440600213017 : Nat.Prime 6425956440600213017 := by
  apply lucas_primality 6425956440600213017 (3 : ZMod 6425956440600213017)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (79, 1), (827, 1), (2658049, 1), (4625431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (79, 1), (827, 1), (2658049, 1), (4625431, 1)] : List FactorBlock).map factorBlockValue).prod) = 6425956440600213017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_827
      · exact prime_oneHundredThirtyOneDY_2658049
      · exact prime_oneHundredThirtyOneDY_4625431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6425956440600213017) ^ 3212978220300106508 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425956440600213017) ^ 81341220767091304 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425956440600213017) ^ 7770201258283208 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425956440600213017) ^ 2417546268184 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6425956440600213017) ^ 1389266522536 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_6496031953767713207 : Nat.Prime 6496031953767713207 := by
  apply lucas_primality 6496031953767713207 (5 : ZMod 6496031953767713207)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (96443, 1), (33678089409121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (96443, 1), (33678089409121, 1)] : List FactorBlock).map factorBlockValue).prod) = 6496031953767713207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_96443
      · exact prime_oneHundredThirtyOneDY_33678089409121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 6496031953767713207) ^ 3248015976883856603 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6496031953767713207) ^ 67356178818242 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6496031953767713207) ^ 192886 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_8849202229893473351 : Nat.Prime 8849202229893473351 := by
  apply lucas_primality 8849202229893473351 (14 : ZMod 8849202229893473351)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (17, 1), (5501, 1), (7937, 1), (34063489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (17, 1), (5501, 1), (7937, 1), (34063489, 1)] : List FactorBlock).map factorBlockValue).prod) = 8849202229893473351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_17
      · exact prime_oneHundredThirtyOneDY_5501
      · exact prime_oneHundredThirtyOneDY_7937
      · exact prime_oneHundredThirtyOneDY_34063489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 8849202229893473351) ^ 4424601114946736675 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 1769840445978694670 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 1264171747127639050 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 520541307640792550 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 1608653377548350 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 1114930355284550 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (14 : ZMod 8849202229893473351) ^ 259785550150 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_10677960213962262553 : Nat.Prime 10677960213962262553 := by
  apply lucas_primality 10677960213962262553 (7 : ZMod 10677960213962262553)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (148305002971698091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (148305002971698091, 1)] : List FactorBlock).map factorBlockValue).prod) = 10677960213962262553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_148305002971698091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 10677960213962262553) ^ 5338980106981131276 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 10677960213962262553) ^ 3559320071320754184 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 10677960213962262553) ^ 72 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_20556692720833778017 : Nat.Prime 20556692720833778017 := by
  apply lucas_primality 20556692720833778017 (10 : ZMod 20556692720833778017)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (23, 1), (1709, 1), (5447686565803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (23, 1), (1709, 1), (5447686565803, 1)] : List FactorBlock).map factorBlockValue).prod) = 20556692720833778017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_1709
      · exact prime_oneHundredThirtyOneDY_5447686565803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 20556692720833778017) ^ 10278346360416889008 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 20556692720833778017) ^ 6852230906944592672 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 20556692720833778017) ^ 893769248731903392 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 20556692720833778017) ^ 12028491937293024 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 20556692720833778017) ^ 3773472 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_22961216158590610759 : Nat.Prime 22961216158590610759 := by
  apply lucas_primality 22961216158590610759 (15 : ZMod 22961216158590610759)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (13, 1), (88589, 1), (302084053259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (13, 1), (88589, 1), (302084053259, 1)] : List FactorBlock).map factorBlockValue).prod) = 22961216158590610759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_88589
      · exact prime_oneHundredThirtyOneDY_302084053259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 22961216158590610759) ^ 11480608079295305379 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 22961216158590610759) ^ 7653738719530203586 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 22961216158590610759) ^ 2087383287144600978 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 22961216158590610759) ^ 1766247396814662366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 22961216158590610759) ^ 259188117696222 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (15 : ZMod 22961216158590610759) ^ 76009362 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_47988045673597037999 : Nat.Prime 47988045673597037999 := by
  apply lucas_primality 47988045673597037999 (7 : ZMod 47988045673597037999)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (113, 1), (19303316843763893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (113, 1), (19303316843763893, 1)] : List FactorBlock).map factorBlockValue).prod) = 47988045673597037999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_113
      · exact prime_oneHundredThirtyOneDY_19303316843763893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 47988045673597037999) ^ 23994022836798518999 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 47988045673597037999) ^ 4362549606690639818 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 47988045673597037999) ^ 424672970562805646 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 47988045673597037999) ^ 2486 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_53377323692674932499 : Nat.Prime 53377323692674932499 := by
  apply lucas_primality 53377323692674932499 (2 : ZMod 53377323692674932499)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33485281, 1), (265675555043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33485281, 1), (265675555043, 1)] : List FactorBlock).map factorBlockValue).prod) = 53377323692674932499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_33485281
      · exact prime_oneHundredThirtyOneDY_265675555043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 53377323692674932499) ^ 26688661846337466249 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53377323692674932499) ^ 17792441230891644166 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53377323692674932499) ^ 1594053330258 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 53377323692674932499) ^ 200911686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_88861515213242230411 : Nat.Prime 88861515213242230411 := by
  apply lucas_primality 88861515213242230411 (7 : ZMod 88861515213242230411)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1693, 1), (7829, 1), (31925019293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1693, 1), (7829, 1), (31925019293, 1)] : List FactorBlock).map factorBlockValue).prod) = 88861515213242230411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_1693
      · exact prime_oneHundredThirtyOneDY_7829
      · exact prime_oneHundredThirtyOneDY_31925019293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88861515213242230411) ^ 44430757606621115205 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 29620505071080743470 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 17772303042648446082 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 12694502173320318630 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 52487604969428370 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 11350302109240290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 88861515213242230411) ^ 2783444370 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_210676417271402330147 : Nat.Prime 210676417271402330147 := by
  apply lucas_primality 210676417271402330147 (2 : ZMod 210676417271402330147)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5147, 1), (20465943002856259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5147, 1), (20465943002856259, 1)] : List FactorBlock).map factorBlockValue).prod) = 210676417271402330147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5147
      · exact prime_oneHundredThirtyOneDY_20465943002856259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 210676417271402330147) ^ 105338208635701165073 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 210676417271402330147) ^ 40931886005712518 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 210676417271402330147) ^ 10294 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_221254800211152960701 : Nat.Prime 221254800211152960701 := by
  apply lucas_primality 221254800211152960701 (2 : ZMod 221254800211152960701)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (1231, 1), (256765463863471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (1231, 1), (256765463863471, 1)] : List FactorBlock).map factorBlockValue).prod) = 221254800211152960701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_1231
      · exact prime_oneHundredThirtyOneDY_256765463863471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221254800211152960701) ^ 110627400105576480350 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 221254800211152960701) ^ 44250960042230592140 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 221254800211152960701) ^ 31607828601593280100 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 221254800211152960701) ^ 179735824704429700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 221254800211152960701) ^ 861700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_247017657931045345987 : Nat.Prime 247017657931045345987 := by
  apply lucas_primality 247017657931045345987 (2 : ZMod 247017657931045345987)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (25741, 1), (14284537, 1), (111965743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (25741, 1), (14284537, 1), (111965743, 1)] : List FactorBlock).map factorBlockValue).prod) = 247017657931045345987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_25741
      · exact prime_oneHundredThirtyOneDY_14284537
      · exact prime_oneHundredThirtyOneDY_111965743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 247017657931045345987) ^ 123508828965522672993 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 247017657931045345987) ^ 82339219310348448662 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 247017657931045345987) ^ 9596272791695946 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 247017657931045345987) ^ 17292661143378 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 247017657931045345987) ^ 2206189601502 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_297688287503788378817 : Nat.Prime 297688287503788378817 := by
  apply lucas_primality 297688287503788378817 (3 : ZMod 297688287503788378817)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (41413, 1), (112316893058863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (41413, 1), (112316893058863, 1)] : List FactorBlock).map factorBlockValue).prod) = 297688287503788378817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_41413
      · exact prime_oneHundredThirtyOneDY_112316893058863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 297688287503788378817) ^ 148844143751894189408 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 297688287503788378817) ^ 7188281155767232 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 297688287503788378817) ^ 2650432 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_476587714873891650661 : Nat.Prime 476587714873891650661 := by
  apply lucas_primality 476587714873891650661 (30 : ZMod 476587714873891650661)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (383, 1), (1321, 1), (168813452789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (383, 1), (1321, 1), (168813452789, 1)] : List FactorBlock).map factorBlockValue).prod) = 476587714873891650661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_383
      · exact prime_oneHundredThirtyOneDY_1321
      · exact prime_oneHundredThirtyOneDY_168813452789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (30 : ZMod 476587714873891650661) ^ 238293857436945825330 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 158862571624630550220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 95317542974778330132 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 15373797253996504860 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 1244354346929221020 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 360777982493483460 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (30 : ZMod 476587714873891650661) ^ 2823161940 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_512594439981027603431 : Nat.Prime 512594439981027603431 := by
  apply lucas_primality 512594439981027603431 (13 : ZMod 512594439981027603431)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (11, 1), (13577, 1), (49031970605467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (11, 1), (13577, 1), (49031970605467, 1)] : List FactorBlock).map factorBlockValue).prod) = 512594439981027603431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_13577
      · exact prime_oneHundredThirtyOneDY_49031970605467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 512594439981027603431) ^ 256297219990513801715 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 512594439981027603431) ^ 102518887996205520686 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 512594439981027603431) ^ 73227777140146800490 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 512594439981027603431) ^ 46599494543729782130 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 512594439981027603431) ^ 37754617366209590 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 512594439981027603431) ^ 10454290 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_516288532070936455709 : Nat.Prime 516288532070936455709 := by
  apply lucas_primality 516288532070936455709 (2 : ZMod 516288532070936455709)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (808651, 1), (159614138877877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (808651, 1), (159614138877877, 1)] : List FactorBlock).map factorBlockValue).prod) = 516288532070936455709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_808651
      · exact prime_oneHundredThirtyOneDY_159614138877877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 516288532070936455709) ^ 258144266035468227854 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 516288532070936455709) ^ 638456555511508 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 516288532070936455709) ^ 3234604 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_875995683065771609441 : Nat.Prime 875995683065771609441 := by
  apply lucas_primality 875995683065771609441 (3 : ZMod 875995683065771609441)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (179, 1), (1772297, 1), (1568916263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (179, 1), (1772297, 1), (1568916263, 1)] : List FactorBlock).map factorBlockValue).prod) = 875995683065771609441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_179
      · exact prime_oneHundredThirtyOneDY_1772297
      · exact prime_oneHundredThirtyOneDY_1568916263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 875995683065771609441) ^ 437997841532885804720 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 875995683065771609441) ^ 175199136613154321888 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 875995683065771609441) ^ 79635971187797419040 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 875995683065771609441) ^ 4893830631652355360 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 875995683065771609441) ^ 494271379495520 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 875995683065771609441) ^ 558344446880 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_894370723344999059899 : Nat.Prime 894370723344999059899 := by
  apply lucas_primality 894370723344999059899 (10 : ZMod 894370723344999059899)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (29, 1), (203311, 1), (1330619392903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (29, 1), (203311, 1), (1330619392903, 1)] : List FactorBlock).map factorBlockValue).prod) = 894370723344999059899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_203311
      · exact prime_oneHundredThirtyOneDY_1330619392903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 894370723344999059899) ^ 447185361672499529949 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 894370723344999059899) ^ 298123574448333019966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 894370723344999059899) ^ 47072143333947318942 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 894370723344999059899) ^ 30840369770517208962 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 894370723344999059899) ^ 4399027712937318 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 894370723344999059899) ^ 672146166 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1471811312763128856301 : Nat.Prime 1471811312763128856301 := by
  apply lucas_primality 1471811312763128856301 (2 : ZMod 1471811312763128856301)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (79, 1), (62101743154562399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (79, 1), (62101743154562399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1471811312763128856301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_62101743154562399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1471811312763128856301) ^ 735905656381564428150 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471811312763128856301) ^ 490603770921042952100 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471811312763128856301) ^ 294362262552625771260 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471811312763128856301) ^ 18630522946368719700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1471811312763128856301) ^ 23700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7614821040204061245641 : Nat.Prime 7614821040204061245641 := by
  apply lucas_primality 7614821040204061245641 (3 : ZMod 7614821040204061245641)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (5791, 1), (2528731931579527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (5791, 1), (2528731931579527, 1)] : List FactorBlock).map factorBlockValue).prod) = 7614821040204061245641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_5791
      · exact prime_oneHundredThirtyOneDY_2528731931579527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7614821040204061245641) ^ 3807410520102030622820 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7614821040204061245641) ^ 1522964208040812249128 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7614821040204061245641) ^ 585755464631081634280 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7614821040204061245641) ^ 1314940604421354040 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 7614821040204061245641) ^ 3011320 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_16579192279206197579933 : Nat.Prime 16579192279206197579933 := by
  apply lucas_primality 16579192279206197579933 (2 : ZMod 16579192279206197579933)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (71, 1), (577559, 1), (14439449377921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (71, 1), (577559, 1), (14439449377921, 1)] : List FactorBlock).map factorBlockValue).prod) = 16579192279206197579933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_71
      · exact prime_oneHundredThirtyOneDY_577559
      · exact prime_oneHundredThirtyOneDY_14439449377921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16579192279206197579933) ^ 8289596139603098789966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16579192279206197579933) ^ 2368456039886599654276 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16579192279206197579933) ^ 233509750411354895492 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16579192279206197579933) ^ 28705625363306948 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 16579192279206197579933) ^ 1148187292 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_40634272779034145213701 : Nat.Prime 40634272779034145213701 := by
  apply lucas_primality 40634272779034145213701 (10 : ZMod 40634272779034145213701)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 2), (53, 1), (851871546730275581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 2), (53, 1), (851871546730275581, 1)] : List FactorBlock).map factorBlockValue).prod) = 40634272779034145213701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_53
      · exact prime_oneHundredThirtyOneDY_851871546730275581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 40634272779034145213701) ^ 20317136389517072606850 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 40634272779034145213701) ^ 13544757593011381737900 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 40634272779034145213701) ^ 8126854555806829042740 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 40634272779034145213701) ^ 766684392057248022900 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 40634272779034145213701) ^ 47700 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_129658511072399171538853 : Nat.Prime 129658511072399171538853 := by
  apply lucas_primality 129658511072399171538853 (2 : ZMod 129658511072399171538853)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (37, 1), (8849202229893473351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (37, 1), (8849202229893473351, 1)] : List FactorBlock).map factorBlockValue).prod) = 129658511072399171538853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_37
      · exact prime_oneHundredThirtyOneDY_8849202229893473351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 129658511072399171538853) ^ 64829255536199585769426 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 129658511072399171538853) ^ 43219503690799723846284 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 129658511072399171538853) ^ 11787137370218106503532 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 129658511072399171538853) ^ 3504284083037815446996 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 129658511072399171538853) ^ 14652 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_206209248732096787642099 : Nat.Prime 206209248732096787642099 := by
  apply lucas_primality 206209248732096787642099 (13 : ZMod 206209248732096787642099)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (50929, 1), (435263, 1), (14489593847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (50929, 1), (435263, 1), (14489593847, 1)] : List FactorBlock).map factorBlockValue).prod) = 206209248732096787642099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_107
      · exact prime_oneHundredThirtyOneDY_50929
      · exact prime_oneHundredThirtyOneDY_435263
      · exact prime_oneHundredThirtyOneDY_14489593847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 206209248732096787642099) ^ 103104624366048393821049 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 206209248732096787642099) ^ 68736416244032262547366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 206209248732096787642099) ^ 1927189240486885865814 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 206209248732096787642099) ^ 4048955383614380562 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 206209248732096787642099) ^ 473757817071740046 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (13 : ZMod 206209248732096787642099) ^ 14231540987934 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_274133557447346204843077 : Nat.Prime 274133557447346204843077 := by
  apply lucas_primality 274133557447346204843077 (5 : ZMod 274133557447346204843077)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7614821040204061245641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7614821040204061245641, 1)] : List FactorBlock).map factorBlockValue).prod) = 274133557447346204843077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_7614821040204061245641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 274133557447346204843077) ^ 137066778723673102421538 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 274133557447346204843077) ^ 91377852482448734947692 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 274133557447346204843077) ^ 36 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_568562383462137576602099 : Nat.Prime 568562383462137576602099 := by
  apply lucas_primality 568562383462137576602099 (2 : ZMod 568562383462137576602099)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1069, 1), (1738003, 1), (1919377, 1), (79718591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1069, 1), (1738003, 1), (1919377, 1), (79718591, 1)] : List FactorBlock).map factorBlockValue).prod) = 568562383462137576602099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_1069
      · exact prime_oneHundredThirtyOneDY_1738003
      · exact prime_oneHundredThirtyOneDY_1919377
      · exact prime_oneHundredThirtyOneDY_79718591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 568562383462137576602099) ^ 284281191731068788301049 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 568562383462137576602099) ^ 531863782471597358842 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 568562383462137576602099) ^ 327135444220831366 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 568562383462137576602099) ^ 296222359370846674 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 568562383462137576602099) ^ 7132117820072078 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_676791477964821438577121 : Nat.Prime 676791477964821438577121 := by
  apply lucas_primality 676791477964821438577121 (6 : ZMod 676791477964821438577121)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (29, 1), (105607, 1), (10687007, 1), (18462481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (29, 1), (105607, 1), (10687007, 1), (18462481, 1)] : List FactorBlock).map factorBlockValue).prod) = 676791477964821438577121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_29
      · exact prime_oneHundredThirtyOneDY_105607
      · exact prime_oneHundredThirtyOneDY_10687007
      · exact prime_oneHundredThirtyOneDY_18462481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 676791477964821438577121) ^ 338395738982410719288560 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 135358295592964287715424 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 96684496852117348368160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 23337637171200739261280 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 6408585396468240160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 63328439661808160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (6 : ZMod 676791477964821438577121) ^ 36657666863127520 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1444828645422968990838931 : Nat.Prime 1444828645422968990838931 := by
  apply lucas_primality 1444828645422968990838931 (2 : ZMod 1444828645422968990838931)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (61, 1), (68147, 1), (28015157, 1), (137849183, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (61, 1), (68147, 1), (28015157, 1), (137849183, 1)] : List FactorBlock).map factorBlockValue).prod) = 1444828645422968990838931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_61
      · exact prime_oneHundredThirtyOneDY_68147
      · exact prime_oneHundredThirtyOneDY_28015157
      · exact prime_oneHundredThirtyOneDY_137849183
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1444828645422968990838931) ^ 722414322711484495419465 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 481609548474322996946310 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 288965729084593798167786 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 23685715498737196571130 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 21201647107326353190 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 51573105423716490 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1444828645422968990838931) ^ 10481227483393710 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_1882727891583838686197617 : Nat.Prime 1882727891583838686197617 := by
  apply lucas_primality 1882727891583838686197617 (10 : ZMod 1882727891583838686197617)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (3323, 1), (45757, 1), (1125571, 1), (17629589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (3323, 1), (45757, 1), (1125571, 1), (17629589, 1)] : List FactorBlock).map factorBlockValue).prod) = 1882727891583838686197617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_13
      · exact prime_oneHundredThirtyOneDY_3323
      · exact prime_oneHundredThirtyOneDY_45757
      · exact prime_oneHundredThirtyOneDY_1125571
      · exact prime_oneHundredThirtyOneDY_17629589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1882727891583838686197617) ^ 941363945791919343098808 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 627575963861279562065872 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 144825222429526052784432 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 566574749197664365392 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 41146226622895703088 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 1672686922090066896 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1882727891583838686197617) ^ 106793634927271344 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2230531602469500079268213 : Nat.Prime 2230531602469500079268213 := by
  apply lucas_primality 2230531602469500079268213 (2 : ZMod 2230531602469500079268213)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (337, 1), (53377323692674932499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (337, 1), (53377323692674932499, 1)] : List FactorBlock).map factorBlockValue).prod) = 2230531602469500079268213 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_337
      · exact prime_oneHundredThirtyOneDY_53377323692674932499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2230531602469500079268213) ^ 1115265801234750039634106 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230531602469500079268213) ^ 71952632337725809008652 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230531602469500079268213) ^ 6618788137891691629876 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2230531602469500079268213) ^ 41788 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2278473560736012857916091 : Nat.Prime 2278473560736012857916091 := by
  apply lucas_primality 2278473560736012857916091 (3 : ZMod 2278473560736012857916091)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (599, 1), (624089, 1), (9674534856313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (599, 1), (624089, 1), (9674534856313, 1)] : List FactorBlock).map factorBlockValue).prod) = 2278473560736012857916091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_7
      · exact prime_oneHundredThirtyOneDY_599
      · exact prime_oneHundredThirtyOneDY_624089
      · exact prime_oneHundredThirtyOneDY_9674534856313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2278473560736012857916091) ^ 1139236780368006428958045 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 759491186912004285972030 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 455694712147202571583218 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 325496222962287551130870 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 3803795593883160029910 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 3650879218726836810 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2278473560736012857916091) ^ 235512465930 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4349865519378450723325049 : Nat.Prime 4349865519378450723325049 := by
  apply lucas_primality 4349865519378450723325049 (3 : ZMod 4349865519378450723325049)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (79, 1), (211, 1), (883, 1), (1606156121713711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (79, 1), (211, 1), (883, 1), (1606156121713711, 1)] : List FactorBlock).map factorBlockValue).prod) = 4349865519378450723325049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_23
      · exact prime_oneHundredThirtyOneDY_79
      · exact prime_oneHundredThirtyOneDY_211
      · exact prime_oneHundredThirtyOneDY_883
      · exact prime_oneHundredThirtyOneDY_1606156121713711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4349865519378450723325049) ^ 2174932759689225361662524 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4349865519378450723325049) ^ 189124587799063074927176 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4349865519378450723325049) ^ 55061588852891781307912 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4349865519378450723325049) ^ 20615476395158534233768 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4349865519378450723325049) ^ 4926235016283636153256 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4349865519378450723325049) ^ 2708245768 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_7538425982841067802579137 : Nat.Prime 7538425982841067802579137 := by
  apply lucas_primality 7538425982841067802579137 (5 : ZMod 7538425982841067802579137)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (269, 1), (178859, 1), (816049246311823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (269, 1), (178859, 1), (816049246311823, 1)] : List FactorBlock).map factorBlockValue).prod) = 7538425982841067802579137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_269
      · exact prime_oneHundredThirtyOneDY_178859
      · exact prime_oneHundredThirtyOneDY_816049246311823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7538425982841067802579137) ^ 3769212991420533901289568 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7538425982841067802579137) ^ 2512808660947022600859712 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7538425982841067802579137) ^ 28023888412048579191744 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7538425982841067802579137) ^ 42147311473513034304 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 7538425982841067802579137) ^ 9237709632 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_22530835294947590631944773 : Nat.Prime 22530835294947590631944773 := by
  apply lucas_primality 22530835294947590631944773 (2 : ZMod 22530835294947590631944773)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (10477963, 1), (10640293, 1), (16840911709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (10477963, 1), (10640293, 1), (16840911709, 1)] : List FactorBlock).map factorBlockValue).prod) = 22530835294947590631944773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_10477963
      · exact prime_oneHundredThirtyOneDY_10640293
      · exact prime_oneHundredThirtyOneDY_16840911709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22530835294947590631944773) ^ 11265417647473795315972386 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22530835294947590631944773) ^ 7510278431649196877314924 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22530835294947590631944773) ^ 2150306819650688844 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22530835294947590631944773) ^ 2117501397278025204 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 22530835294947590631944773) ^ 1337863156357908 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_23251307884322134514935951 : Nat.Prime 23251307884322134514935951 := by
  apply lucas_primality 23251307884322134514935951 (7 : ZMod 23251307884322134514935951)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (11, 1), (941, 1), (312673, 1), (2171881, 1), (2450219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (11, 1), (941, 1), (312673, 1), (2171881, 1), (2450219, 1)] : List FactorBlock).map factorBlockValue).prod) = 23251307884322134514935951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_941
      · exact prime_oneHundredThirtyOneDY_312673
      · exact prime_oneHundredThirtyOneDY_2171881
      · exact prime_oneHundredThirtyOneDY_2450219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23251307884322134514935951) ^ 11625653942161067257467975 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 7750435961440711504978650 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 4650261576864426902987190 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 2113755262211103137721450 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 24709147592265817762950 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 74363017863141795150 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 10705608587359129950 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 23251307884322134514935951) ^ 9489481505254075050 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_25397993082563092489994813 : Nat.Prime 25397993082563092489994813 := by
  apply lucas_primality 25397993082563092489994813 (2 : ZMod 25397993082563092489994813)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (337, 1), (6229, 1), (15307, 1), (178037, 1), (1109917829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (337, 1), (6229, 1), (15307, 1), (178037, 1), (1109917829, 1)] : List FactorBlock).map factorBlockValue).prod) = 25397993082563092489994813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_337
      · exact prime_oneHundredThirtyOneDY_6229
      · exact prime_oneHundredThirtyOneDY_15307
      · exact prime_oneHundredThirtyOneDY_178037
      · exact prime_oneHundredThirtyOneDY_1109917829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25397993082563092489994813) ^ 12698996541281546244997406 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 25397993082563092489994813) ^ 75364964636685734391676 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 25397993082563092489994813) ^ 4077378886267955127628 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 25397993082563092489994813) ^ 1659240418276807505716 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 25397993082563092489994813) ^ 142655701245039472076 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 25397993082563092489994813) ^ 22882768813116428 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_67220903566610129342008841 : Nat.Prime 67220903566610129342008841 := by
  apply lucas_primality 67220903566610129342008841 (3 : ZMod 67220903566610129342008841)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (1879, 1), (894370723344999059899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (1879, 1), (894370723344999059899, 1)] : List FactorBlock).map factorBlockValue).prod) = 67220903566610129342008841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_1879
      · exact prime_oneHundredThirtyOneDY_894370723344999059899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 67220903566610129342008841) ^ 33610451783305064671004420 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 67220903566610129342008841) ^ 13444180713322025868401768 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 67220903566610129342008841) ^ 35774828933799962395960 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 67220903566610129342008841) ^ 75160 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_102771706580935459856661161 : Nat.Prime 102771706580935459856661161 := by
  apply lucas_primality 102771706580935459856661161 (3 : ZMod 102771706580935459856661161)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (224729039, 1), (11432846756058911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (224729039, 1), (11432846756058911, 1)] : List FactorBlock).map factorBlockValue).prod) = 102771706580935459856661161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_224729039
      · exact prime_oneHundredThirtyOneDY_11432846756058911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 102771706580935459856661161) ^ 51385853290467729928330580 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 102771706580935459856661161) ^ 20554341316187091971332232 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 102771706580935459856661161) ^ 457313870242356440 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 102771706580935459856661161) ^ 8989161560 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_170194463535681030773613593 : Nat.Prime 170194463535681030773613593 := by
  apply lucas_primality 170194463535681030773613593 (3 : ZMod 170194463535681030773613593)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (83, 1), (8221, 1), (28229, 1), (58321, 1), (18937918577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (83, 1), (8221, 1), (28229, 1), (58321, 1), (18937918577, 1)] : List FactorBlock).map factorBlockValue).prod) = 170194463535681030773613593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_83
      · exact prime_oneHundredThirtyOneDY_8221
      · exact prime_oneHundredThirtyOneDY_28229
      · exact prime_oneHundredThirtyOneDY_58321
      · exact prime_oneHundredThirtyOneDY_18937918577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 170194463535681030773613593) ^ 85097231767840515386806796 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170194463535681030773613593) ^ 2050535705249169045465224 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170194463535681030773613593) ^ 20702404030614405884152 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170194463535681030773613593) ^ 6029064562530767323448 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170194463535681030773613593) ^ 2918236373444917452952 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 170194463535681030773613593) ^ 8986967751692696 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_192633037086405146771129813 : Nat.Prime 192633037086405146771129813 := by
  apply lucas_primality 192633037086405146771129813 (2 : ZMod 192633037086405146771129813)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (857, 1), (1171, 1), (47988045673597037999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (857, 1), (1171, 1), (47988045673597037999, 1)] : List FactorBlock).map factorBlockValue).prod) = 192633037086405146771129813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_857
      · exact prime_oneHundredThirtyOneDY_1171
      · exact prime_oneHundredThirtyOneDY_47988045673597037999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 192633037086405146771129813) ^ 96316518543202573385564906 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 192633037086405146771129813) ^ 224776005935128525987316 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 192633037086405146771129813) ^ 164503020569090646260572 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 192633037086405146771129813) ^ 4014188 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_470750643822096468097229087 : Nat.Prime 470750643822096468097229087 := by
  apply lucas_primality 470750643822096468097229087 (5 : ZMod 470750643822096468097229087)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (327799, 1), (1694133731, 1), (9856827529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (327799, 1), (1694133731, 1), (9856827529, 1)] : List FactorBlock).map factorBlockValue).prod) = 470750643822096468097229087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_43
      · exact prime_oneHundredThirtyOneDY_327799
      · exact prime_oneHundredThirtyOneDY_1694133731
      · exact prime_oneHundredThirtyOneDY_9856827529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 470750643822096468097229087) ^ 235375321911048234048614543 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470750643822096468097229087) ^ 10947689391211545769703002 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470750643822096468097229087) ^ 1436095423787432140114 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470750643822096468097229087) ^ 277871005817365706 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (5 : ZMod 470750643822096468097229087) ^ 47758839488373934 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2458364473293170444507751899 : Nat.Prime 2458364473293170444507751899 := by
  apply lucas_primality 2458364473293170444507751899 (2 : ZMod 2458364473293170444507751899)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (229, 1), (18617, 1), (523169, 1), (7549292142089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (229, 1), (18617, 1), (523169, 1), (7549292142089, 1)] : List FactorBlock).map factorBlockValue).prod) = 2458364473293170444507751899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_73
      · exact prime_oneHundredThirtyOneDY_229
      · exact prime_oneHundredThirtyOneDY_18617
      · exact prime_oneHundredThirtyOneDY_523169
      · exact prime_oneHundredThirtyOneDY_7549292142089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2458364473293170444507751899) ^ 1229182236646585222253875949 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458364473293170444507751899) ^ 33676225661550280061750026 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458364473293170444507751899) ^ 10735216040581530325361362 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458364473293170444507751899) ^ 132049442621967580410794 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458364473293170444507751899) ^ 4698987274271163705242 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2458364473293170444507751899) ^ 325641719385482 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_2815944760317631600072515811 : Nat.Prime 2815944760317631600072515811 := by
  apply lucas_primality 2815944760317631600072515811 (2 : ZMod 2815944760317631600072515811)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (5655420833, 1), (199967702415493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (5655420833, 1), (199967702415493, 1)] : List FactorBlock).map factorBlockValue).prod) = 2815944760317631600072515811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_83
      · exact prime_oneHundredThirtyOneDY_5655420833
      · exact prime_oneHundredThirtyOneDY_199967702415493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2815944760317631600072515811) ^ 1407972380158815800036257905 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2815944760317631600072515811) ^ 938648253439210533357505270 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2815944760317631600072515811) ^ 563188952063526320014503162 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2815944760317631600072515811) ^ 33927045305031706024970070 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2815944760317631600072515811) ^ 497919579014577570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2815944760317631600072515811) ^ 14081997874170 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_4839905056795929312624636551 : Nat.Prime 4839905056795929312624636551 := by
  apply lucas_primality 4839905056795929312624636551 (7 : ZMod 4839905056795929312624636551)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (131, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (131, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 4839905056795929312624636551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_131
      · exact prime_oneHundredThirtyOneDY_171401
      · exact prime_oneHundredThirtyOneDY_714027719
      · exact prime_oneHundredThirtyOneDY_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4839905056795929312624636551) ^ 2419952528397964656312318275 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4839905056795929312624636551) ^ 967981011359185862524927310 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4839905056795929312624636551) ^ 36945840128213200859730050 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4839905056795929312624636551) ^ 28237321000437157966550 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4839905056795929312624636551) ^ 6778315362286277450 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4839905056795929312624636551) ^ 801622176171289450 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_12906413484789144833665697473 : Nat.Prime 12906413484789144833665697473 := by
  apply lucas_primality 12906413484789144833665697473 (7 : ZMod 12906413484789144833665697473)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (67220903566610129342008841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (67220903566610129342008841, 1)] : List FactorBlock).map factorBlockValue).prod) = 12906413484789144833665697473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_67220903566610129342008841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 12906413484789144833665697473) ^ 6453206742394572416832848736 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 12906413484789144833665697473) ^ 4302137828263048277888565824 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 12906413484789144833665697473) ^ 192 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_14079723801588158000362579061 : Nat.Prime 14079723801588158000362579061 := by
  apply lucas_primality 14079723801588158000362579061 (3 : ZMod 14079723801588158000362579061)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (31, 1), (809, 1), (3539, 1), (16073, 1), (25973041894399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (31, 1), (809, 1), (3539, 1), (16073, 1), (25973041894399, 1)] : List FactorBlock).map factorBlockValue).prod) = 14079723801588158000362579061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_809
      · exact prime_oneHundredThirtyOneDY_3539
      · exact prime_oneHundredThirtyOneDY_16073
      · exact prime_oneHundredThirtyOneDY_25973041894399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14079723801588158000362579061) ^ 7039861900794079000181289530 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 2815944760317631600072515812 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 741038094820429368440135740 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 454184638760908322592341260 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 17403861312222692213056340 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 3978446962867521333812540 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 875986051240475206891220 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (3 : ZMod 14079723801588158000362579061) ^ 542089904556940 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_17208551313052193111554263289 : Nat.Prime 17208551313052193111554263289 := by
  apply lucas_primality 17208551313052193111554263289 (7 : ZMod 17208551313052193111554263289)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 1), (122033, 1), (50117909, 1), (1987059294019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 1), (122033, 1), (50117909, 1), (1987059294019, 1)] : List FactorBlock).map factorBlockValue).prod) = 17208551313052193111554263289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_3
      · exact prime_oneHundredThirtyOneDY_59
      · exact prime_oneHundredThirtyOneDY_122033
      · exact prime_oneHundredThirtyOneDY_50117909
      · exact prime_oneHundredThirtyOneDY_1987059294019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 17208551313052193111554263289) ^ 8604275656526096555777131644 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 17208551313052193111554263289) ^ 5736183771017397703851421096 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 17208551313052193111554263289) ^ 291670361238172764602614632 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 17208551313052193111554263289) ^ 141015555735351856559736 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 17208551313052193111554263289) ^ 343361318467061207832 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 17208551313052193111554263289) ^ 8660310925219752 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyOneDY_77438480908734869001994184831 : Nat.Prime 77438480908734869001994184831 := by
  apply lucas_primality 77438480908734869001994184831 (7 : ZMod 77438480908734869001994184831)
  · rw [← oneHundredThirtyOneDYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (809, 1), (3539, 1), (16073, 1), (25973041894399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (31, 1), (809, 1), (3539, 1), (16073, 1), (25973041894399, 1)] : List FactorBlock).map factorBlockValue).prod) = 77438480908734869001994184831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyOneDY_2
      · exact prime_oneHundredThirtyOneDY_5
      · exact prime_oneHundredThirtyOneDY_11
      · exact prime_oneHundredThirtyOneDY_19
      · exact prime_oneHundredThirtyOneDY_31
      · exact prime_oneHundredThirtyOneDY_809
      · exact prime_oneHundredThirtyOneDY_3539
      · exact prime_oneHundredThirtyOneDY_16073
      · exact prime_oneHundredThirtyOneDY_25973041894399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 77438480908734869001994184831) ^ 38719240454367434500997092415 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 15487696181746973800398836966 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 7039861900794079000181289530 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 4075709521512361526420746570 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 2498015513184995774257876930 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 95721237217224807171809870 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 21881458295771367335968970 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 4817923281822613637901710 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide
    · change (7 : ZMod 77438480908734869001994184831) ^ 2981494475063170 ≠ 1
      rw [← oneHundredThirtyOneDYFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369600 : Nat.totient 154876961817469738003988369600 = 61477519198422436445905920000 := by
  rw [← show ((([(2, 6), (5, 2), (131, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_131, prime_oneHundredThirtyOneDY_171401, prime_oneHundredThirtyOneDY_714027719, prime_oneHundredThirtyOneDY_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369601 : Nat.totient 154876961817469738003988369601 = 103251307878313158669325579728 := by
  rw [← show ((([(3, 2), (17208551313052193111554263289, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_17208551313052193111554263289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369602 : Nat.totient 154876961817469738003988369602 = 66240655767145916457917629680 := by
  rw [← show ((([(2, 1), (7, 1), (491, 1), (22530835294947590631944773, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_491, prime_oneHundredThirtyOneDY_22530835294947590631944773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369603 : Nat.totient 154876961817469738003988369603 = 146156925522974336808291384480 := by
  rw [← show ((([(19, 1), (431, 1), (643, 1), (277247, 1), (106090896923230187, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_431, prime_oneHundredThirtyOneDY_643, prime_oneHundredThirtyOneDY_277247, prime_oneHundredThirtyOneDY_106090896923230187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369604 : Nat.totient 154876961817469738003988369604 = 47576936677186170976840335360 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (1213, 1), (1249, 1), (457271, 1), (1433063133352517, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_1213, prime_oneHundredThirtyOneDY_1249, prime_oneHundredThirtyOneDY_457271, prime_oneHundredThirtyOneDY_1433063133352517]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369605 : Nat.totient 154876961817469738003988369605 = 112637790412705264002900632400 := by
  rw [← show ((([(5, 1), (11, 1), (2815944760317631600072515811, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_2815944760317631600072515811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369606 : Nat.totient 154876961817469738003988369606 = 77400943077079061803510792704 := by
  rw [← show ((([(2, 1), (2063, 1), (105350503, 1), (470948939, 1), (756566593, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_2063, prime_oneHundredThirtyOneDY_105350503, prime_oneHundredThirtyOneDY_470948939, prime_oneHundredThirtyOneDY_756566593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369607 : Nat.totient 154876961817469738003988369607 = 97175838702553915131585331200 := by
  rw [← show ((([(3, 1), (17, 1), (86561, 1), (134399, 1), (5672011, 1), (46021553833, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_86561, prime_oneHundredThirtyOneDY_134399, prime_oneHundredThirtyOneDY_5672011, prime_oneHundredThirtyOneDY_46021553833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369608 : Nat.totient 154876961817469738003988369608 = 77438480904115920111798561600 := by
  rw [← show ((([(2, 3), (16765390541, 1), (1154737205783515261, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_16765390541, prime_oneHundredThirtyOneDY_1154737205783515261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369609 : Nat.totient 154876961817469738003988369609 = 132751681548681109590334174824 := by
  rw [← show ((([(7, 2), (14508231763, 1), (217859376279492707, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_14508231763, prime_oneHundredThirtyOneDY_217859376279492707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369610 : Nat.totient 154876961817469738003988369610 = 39873468651599649525502708224 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (29, 1), (13759, 1), (122100373, 1), (35321769486343, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_29, prime_oneHundredThirtyOneDY_13759, prime_oneHundredThirtyOneDY_122100373, prime_oneHundredThirtyOneDY_35321769486343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369611 : Nat.totient 154876961817469738003988369611 = 154853710509585415869473427000 := by
  rw [← show ((([(6661, 1), (23251307884322134514935951, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_6661, prime_oneHundredThirtyOneDY_23251307884322134514935951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369612 : Nat.totient 154876961817469738003988369612 = 76742817116673116535857633280 := by
  rw [← show ((([(2, 2), (113, 1), (7517, 1), (489161, 1), (93186287800952263, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_113, prime_oneHundredThirtyOneDY_7517, prime_oneHundredThirtyOneDY_489161, prime_oneHundredThirtyOneDY_93186287800952263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369613 : Nat.totient 154876961817469738003988369613 = 103250759611198263976915516944 := by
  rw [← show ((([(3, 1), (188323, 1), (274133557447346204843077, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_188323, prime_oneHundredThirtyOneDY_274133557447346204843077]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369614 : Nat.totient 154876961817469738003988369614 = 77437036080089446033003292280 := by
  rw [← show ((([(2, 1), (53597, 1), (1444828645422968990838931, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_53597, prime_oneHundredThirtyOneDY_1444828645422968990838931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369615 : Nat.totient 154876961817469738003988369615 = 123901569453974366924771198112 := by
  rw [← show ((([(5, 1), (151754627593039, 1), (204114977281357, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_151754627593039, prime_oneHundredThirtyOneDY_204114977281357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369616 : Nat.totient 154876961817469738003988369616 = 39562288087072903657344000000 := by
  rw [← show ((([(2, 4), (3, 1), (7, 1), (11, 1), (71, 1), (401, 1), (1471811312763128856301, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_71, prime_oneHundredThirtyOneDY_401, prime_oneHundredThirtyOneDY_1471811312763128856301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369617 : Nat.totient 154876961817469738003988369617 = 142935792059019686742177477120 := by
  rw [← show ((([(13, 2), (5717, 1), (56041, 1), (2860395245590249469, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_5717, prime_oneHundredThirtyOneDY_56041, prime_oneHundredThirtyOneDY_2860395245590249469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369618 : Nat.totient 154876961817469738003988369618 = 77438480611046581497945673216 := by
  rw [← show ((([(2, 1), (260132777, 1), (297688287503788378817, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_260132777, prime_oneHundredThirtyOneDY_297688287503788378817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369619 : Nat.totient 154876961817469738003988369619 = 100460731989693897075475029600 := by
  rw [← show ((([(3, 3), (37, 1), (11370814037111, 1), (13634203611571, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_37, prime_oneHundredThirtyOneDY_11370814037111, prime_oneHundredThirtyOneDY_13634203611571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369620 : Nat.totient 154876961817469738003988369620 = 61946868235056478174125645824 := by
  rw [← show ((([(2, 2), (5, 1), (22409, 1), (53777, 1), (6425956440600213017, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_22409, prime_oneHundredThirtyOneDY_53777, prime_oneHundredThirtyOneDY_6425956440600213017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369621 : Nat.totient 154876961817469738003988369621 = 146704897556955265978510403376 := by
  rw [← show ((([(23, 1), (103, 1), (58168701863, 1), (1123912206566243, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_23, prime_oneHundredThirtyOneDY_103, prime_oneHundredThirtyOneDY_58168701863, prime_oneHundredThirtyOneDY_1123912206566243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369622 : Nat.totient 154876961817469738003988369622 = 48908506673797316546332923648 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (6448609, 1), (210676417271402330147, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_6448609, prime_oneHundredThirtyOneDY_210676417271402330147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369623 : Nat.totient 154876961817469738003988369623 = 129927177694898625194835227736 := by
  rw [← show ((([(7, 1), (47, 1), (470750643822096468097229087, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_47, prime_oneHundredThirtyOneDY_470750643822096468097229087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369624 : Nat.totient 154876961817469738003988369624 = 72650342396284061230410301440 := by
  rw [← show ((([(2, 3), (17, 1), (421, 2), (1223, 1), (296353, 1), (635707, 1), (27886303, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_421, prime_oneHundredThirtyOneDY_1223, prime_oneHundredThirtyOneDY_296353, prime_oneHundredThirtyOneDY_635707, prime_oneHundredThirtyOneDY_27886303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369625 : Nat.totient 154876961817469738003988369625 = 82128303498964911367039328000 := by
  rw [← show ((([(3, 1), (5, 3), (179, 1), (11087, 1), (21191, 1), (9820577400857933, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_179, prime_oneHundredThirtyOneDY_11087, prime_oneHundredThirtyOneDY_21191, prime_oneHundredThirtyOneDY_9820577400857933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369626 : Nat.totient 154876961817469738003988369626 = 76640146039399872524907521664 := by
  rw [← show ((([(2, 1), (97, 1), (5247251143, 1), (152143442913768203, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_97, prime_oneHundredThirtyOneDY_5247251143, prime_oneHundredThirtyOneDY_152143442913768203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369627 : Nat.totient 154876961817469738003988369627 = 139769520950072225405059177600 := by
  rw [← show ((([(11, 1), (137, 1), (102771706580935459856661161, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_137, prime_oneHundredThirtyOneDY_102771706580935459856661161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369628 : Nat.totient 154876961817469738003988369628 = 51308929626373297471414884480 := by
  rw [← show ((([(2, 2), (3, 2), (163, 1), (23930939, 1), (143009131, 1), (7712109869, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_163, prime_oneHundredThirtyOneDY_23930939, prime_oneHundredThirtyOneDY_143009131, prime_oneHundredThirtyOneDY_7712109869]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369629 : Nat.totient 154876961817469738003988369629 = 148557601891970159660964460800 := by
  rw [← show ((([(31, 1), (127, 1), (1039, 1), (3303523, 1), (11461158628235761, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_31, prime_oneHundredThirtyOneDY_127, prime_oneHundredThirtyOneDY_1039, prime_oneHundredThirtyOneDY_3303523, prime_oneHundredThirtyOneDY_11461158628235761]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369630 : Nat.totient 154876961817469738003988369630 = 49016005498276136862800714496 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (13, 1), (170194463535681030773613593, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_170194463535681030773613593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369631 : Nat.totient 154876961817469738003988369631 = 103233733961358671358493968960 := by
  rw [← show ((([(3, 1), (5881, 1), (6017159, 1), (1458891180555799163, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5881, prime_oneHundredThirtyOneDY_6017159, prime_oneHundredThirtyOneDY_1458891180555799163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369632 : Nat.totient 154876961817469738003988369632 = 77438480908734869001994184800 := by
  rw [← show ((([(2, 5), (4839905056795929312624636551, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_4839905056795929312624636551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369633 : Nat.totient 154876961817469738003988369633 = 152994065167296962236027621728 := by
  rw [← show ((([(83, 1), (9049, 1), (206209248732096787642099, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_83, prime_oneHundredThirtyOneDY_9049, prime_oneHundredThirtyOneDY_206209248732096787642099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369634 : Nat.totient 154876961817469738003988369634 = 51621096992035107308946935040 := by
  rw [← show ((([(2, 1), (3, 1), (11329, 1), (2278473560736012857916091, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_11329, prime_oneHundredThirtyOneDY_2278473560736012857916091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369635 : Nat.totient 154876961817469738003988369635 = 123899748842121730215430227040 := by
  rw [← show ((([(5, 1), (69383, 1), (3555311, 1), (125570072697136079, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_69383, prime_oneHundredThirtyOneDY_3555311, prime_oneHundredThirtyOneDY_125570072697136079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369636 : Nat.totient 154876961817469738003988369636 = 75359984091438734607436677120 := by
  rw [← show ((([(2, 2), (41, 1), (509, 1), (1889, 1), (54907, 1), (2032553, 1), (8800830119, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_41, prime_oneHundredThirtyOneDY_509, prime_oneHundredThirtyOneDY_1889, prime_oneHundredThirtyOneDY_54907, prime_oneHundredThirtyOneDY_2032553, prime_oneHundredThirtyOneDY_8800830119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369637 : Nat.totient 154876961817469738003988369637 = 88501121038554136002279068328 := by
  rw [← show ((([(3, 2), (7, 1), (2458364473293170444507751899, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_2458364473293170444507751899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369638 : Nat.totient 154876961817469738003988369638 = 67931394773498606709498585600 := by
  rw [← show ((([(2, 1), (11, 1), (43, 1), (149, 1), (191, 1), (8999, 1), (19867, 1), (32177292986549, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_43, prime_oneHundredThirtyOneDY_149, prime_oneHundredThirtyOneDY_191, prime_oneHundredThirtyOneDY_8999, prime_oneHundredThirtyOneDY_19867, prime_oneHundredThirtyOneDY_32177292986549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369639 : Nat.totient 154876961817469738003988369639 = 148442847715795994175487647744 := by
  rw [← show ((([(29, 1), (167, 1), (907, 1), (6983, 1), (18353, 1), (30493, 1), (9022269677, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_29, prime_oneHundredThirtyOneDY_167, prime_oneHundredThirtyOneDY_907, prime_oneHundredThirtyOneDY_6983, prime_oneHundredThirtyOneDY_18353, prime_oneHundredThirtyOneDY_30493, prime_oneHundredThirtyOneDY_9022269677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369640 : Nat.totient 154876961817469738003988369640 = 41278865824030389181695703040 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (1907, 1), (676791477964821438577121, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_1907, prime_oneHundredThirtyOneDY_676791477964821438577121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369641 : Nat.totient 154876961817469738003988369641 = 137711513910654092473501731840 := by
  rw [← show ((([(17, 1), (19, 1), (691, 1), (757, 1), (124343, 1), (7372062866764987, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_691, prime_oneHundredThirtyOneDY_757, prime_oneHundredThirtyOneDY_124343, prime_oneHundredThirtyOneDY_7372062866764987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369642 : Nat.totient 154876961817469738003988369642 = 75463507609118001615593594880 := by
  rw [← show ((([(2, 1), (53, 1), (281, 1), (337, 1), (4007, 1), (254513179, 1), (15129170477, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_53, prime_oneHundredThirtyOneDY_281, prime_oneHundredThirtyOneDY_337, prime_oneHundredThirtyOneDY_4007, prime_oneHundredThirtyOneDY_254513179, prime_oneHundredThirtyOneDY_15129170477]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369643 : Nat.totient 154876961817469738003988369643 = 95308899576166738913081647104 := by
  rw [← show ((([(3, 1), (13, 1), (24985046173, 1), (158943238354202369, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_24985046173, prime_oneHundredThirtyOneDY_158943238354202369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369644 : Nat.totient 154876961817469738003988369644 = 63322413476957853069893025600 := by
  rw [← show ((([(2, 2), (7, 1), (23, 1), (379, 1), (40471351, 1), (15678844077625319, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_23, prime_oneHundredThirtyOneDY_379, prime_oneHundredThirtyOneDY_40471351, prime_oneHundredThirtyOneDY_15678844077625319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369645 : Nat.totient 154876961817469738003988369645 = 123884169991898276600297367040 := by
  rw [← show ((([(5, 1), (7121, 1), (4349865519378450723325049, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_7121, prime_oneHundredThirtyOneDY_4349865519378450723325049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369646 : Nat.totient 154876961817469738003988369646 = 51625653939150669511329608352 := by
  rw [← show ((([(2, 1), (3, 4), (9572918156687, 1), (99868254680009, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_9572918156687, prime_oneHundredThirtyOneDY_99868254680009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369647 : Nat.totient 154876961817469738003988369647 = 152746024187994857619746142528 := by
  rw [← show ((([(73, 1), (16363, 1), (129658511072399171538853, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_73, prime_oneHundredThirtyOneDY_16363, prime_oneHundredThirtyOneDY_129658511072399171538853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369648 : Nat.totient 154876961817469738003988369648 = 77026891339722817524028032000 := by
  rw [← show ((([(2, 4), (271, 1), (631, 1), (21589, 1), (1047586381, 1), (2502913367, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_271, prime_oneHundredThirtyOneDY_631, prime_oneHundredThirtyOneDY_21589, prime_oneHundredThirtyOneDY_1047586381, prime_oneHundredThirtyOneDY_2502913367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369649 : Nat.totient 154876961817469738003988369649 = 93864298519960250537546960000 := by
  rw [← show ((([(3, 1), (11, 1), (185051, 1), (4792331, 1), (5292180373423913, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_185051, prime_oneHundredThirtyOneDY_4792331, prime_oneHundredThirtyOneDY_5292180373423913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369650 : Nat.totient 154876961817469738003988369650 = 61950784726893361210200282000 := by
  rw [← show ((([(2, 1), (5, 2), (655419022243, 1), (4726044150731051, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_655419022243, prime_oneHundredThirtyOneDY_4726044150731051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369651 : Nat.totient 154876961817469738003988369651 = 130495883497937850348289887648 := by
  rw [← show ((([(7, 1), (59, 1), (22619, 1), (16579192279206197579933, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_59, prime_oneHundredThirtyOneDY_22619, prime_oneHundredThirtyOneDY_16579192279206197579933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369652 : Nat.totient 154876961817469738003988369652 = 50855121790810958747578270368 := by
  rw [← show ((([(2, 2), (3, 1), (67, 1), (192633037086405146771129813, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_67, prime_oneHundredThirtyOneDY_192633037086405146771129813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369653 : Nat.totient 154876961817469738003988369653 = 154876914731794997977089349200 := by
  rw [← show ((([(3314651, 1), (429372389, 1), (108821547845827, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3314651, prime_oneHundredThirtyOneDY_429372389, prime_oneHundredThirtyOneDY_108821547845827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369654 : Nat.totient 154876961817469738003988369654 = 77436598180843285163307946080 := by
  rw [← show ((([(2, 1), (41131, 1), (1882727891583838686197617, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_41131, prime_oneHundredThirtyOneDY_1882727891583838686197617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369655 : Nat.totient 154876961817469738003988369655 = 82547513544191258933557989696 := by
  rw [← show ((([(3, 2), (5, 1), (1543, 1), (2230531602469500079268213, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_1543, prime_oneHundredThirtyOneDY_2230531602469500079268213]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369656 : Nat.totient 154876961817469738003988369656 = 69548960017494771322105958400 := by
  rw [← show ((([(2, 3), (13, 1), (37, 1), (89477, 1), (313277771, 1), (1435855587641, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_37, prime_oneHundredThirtyOneDY_89477, prime_oneHundredThirtyOneDY_313277771, prime_oneHundredThirtyOneDY_1435855587641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369657 : Nat.totient 154876961817469738003988369657 = 154876961570452080072316036260 := by
  rw [← show ((([(626987411, 1), (247017657931045345987, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_626987411, prime_oneHundredThirtyOneDY_247017657931045345987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369658 : Nat.totient 154876961817469738003988369658 = 40964830267374821281945927680 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (17, 1), (61, 1), (4662433, 1), (108955242046533067, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_61, prime_oneHundredThirtyOneDY_4662433, prime_oneHundredThirtyOneDY_108955242046533067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369659 : Nat.totient 154876961817469738003988369659 = 154080821285487310924945778400 := by
  rw [← show ((([(199, 1), (14951, 1), (20389, 1), (2553098537497366319, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_199, prime_oneHundredThirtyOneDY_14951, prime_oneHundredThirtyOneDY_20389, prime_oneHundredThirtyOneDY_2553098537497366319]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369660 : Nat.totient 154876961817469738003988369660 = 51552018660153863339963596800 := by
  rw [← show ((([(2, 2), (5, 1), (11, 1), (19, 1), (31, 1), (809, 1), (3539, 1), (16073, 1), (25973041894399, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_31, prime_oneHundredThirtyOneDY_809, prime_oneHundredThirtyOneDY_3539, prime_oneHundredThirtyOneDY_16073, prime_oneHundredThirtyOneDY_25973041894399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369661 : Nat.totient 154876961817469738003988369661 = 102981722218007908139110891184 := by
  rw [← show ((([(3, 1), (383, 1), (2196712776227, 1), (61361153623307, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_383, prime_oneHundredThirtyOneDY_2196712776227, prime_oneHundredThirtyOneDY_61361153623307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369662 : Nat.totient 154876961817469738003988369662 = 77438480908734869001994184830 := by
  rw [← show ((([(2, 1), (77438480908734869001994184831, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_77438480908734869001994184831]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369663 : Nat.totient 154876961817469738003988369663 = 154876961304875298022658622960 := by
  rw [← show ((([(302143273, 1), (512594439981027603431, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_302143273, prime_oneHundredThirtyOneDY_512594439981027603431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369664 : Nat.totient 154876961817469738003988369664 = 51625653939156579334662789120 := by
  rw [← show ((([(2, 8), (3, 2), (67220903566610129342008841, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_67220903566610129342008841]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369665 : Nat.totient 154876961817469738003988369665 = 106020423022676777575472968704 := by
  rw [← show ((([(5, 1), (7, 1), (587, 1), (7538425982841067802579137, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_587, prime_oneHundredThirtyOneDY_7538425982841067802579137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369666 : Nat.totient 154876961817469738003988369666 = 77176253061142177138523712000 := by
  rw [← show ((([(2, 1), (701, 1), (823, 1), (2383, 1), (3191, 1), (64499, 1), (273675010793, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_701, prime_oneHundredThirtyOneDY_823, prime_oneHundredThirtyOneDY_2383, prime_oneHundredThirtyOneDY_3191, prime_oneHundredThirtyOneDY_64499, prime_oneHundredThirtyOneDY_273675010793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369667 : Nat.totient 154876961817469738003988369667 = 98319229676164260829632146976 := by
  rw [← show ((([(3, 1), (23, 1), (223, 1), (8595383, 1), (1171028955262083727, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_23, prime_oneHundredThirtyOneDY_223, prime_oneHundredThirtyOneDY_8595383, prime_oneHundredThirtyOneDY_1171028955262083727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369668 : Nat.totient 154876961817469738003988369668 = 74768188463044639832845621248 := by
  rw [← show ((([(2, 2), (29, 1), (133173810229, 1), (10025591520348737, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_29, prime_oneHundredThirtyOneDY_133173810229, prime_oneHundredThirtyOneDY_10025591520348737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369669 : Nat.totient 154876961817469738003988369669 = 139810521469241025545926268160 := by
  rw [← show ((([(13, 1), (79, 1), (109, 1), (2903, 1), (476587714873891650661, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_79, prime_oneHundredThirtyOneDY_109, prime_oneHundredThirtyOneDY_2903, prime_oneHundredThirtyOneDY_476587714873891650661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369670 : Nat.totient 154876961817469738003988369670 = 40421784686701324652050583808 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (47, 1), (10286779, 1), (10677960213962262553, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_47, prime_oneHundredThirtyOneDY_10286779, prime_oneHundredThirtyOneDY_10677960213962262553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369671 : Nat.totient 154876961817469738003988369671 = 140797238015881580003625790600 := by
  rw [← show ((([(11, 1), (14079723801588158000362579061, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_14079723801588158000362579061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369672 : Nat.totient 154876961817469738003988369672 = 65630044814794053171793053696 := by
  rw [← show ((([(2, 3), (7, 1), (89, 1), (209636714207, 1), (148231820665969, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_89, prime_oneHundredThirtyOneDY_209636714207, prime_oneHundredThirtyOneDY_148231820665969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369673 : Nat.totient 154876961817469738003988369673 = 102047079713747005795135795200 := by
  rw [← show ((([(3, 3), (101, 1), (577, 1), (21419, 1), (1613137927, 1), (2848755499, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_101, prime_oneHundredThirtyOneDY_577, prime_oneHundredThirtyOneDY_21419, prime_oneHundredThirtyOneDY_1613137927, prime_oneHundredThirtyOneDY_2848755499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369674 : Nat.totient 154876961817469738003988369674 = 77413082915652305909504186976 := by
  rw [← show ((([(2, 1), (3049, 1), (25397993082563092489994813, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3049, prime_oneHundredThirtyOneDY_25397993082563092489994813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369675 : Nat.totient 154876961817469738003988369675 = 116613241832788718510598336000 := by
  rw [← show ((([(5, 2), (17, 1), (18666142021, 1), (19522854821151991, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_18666142021, prime_oneHundredThirtyOneDY_19522854821151991]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369676 : Nat.totient 154876961817469738003988369676 = 51625653939156579334662789888 := by
  rw [← show ((([(2, 2), (3, 1), (12906413484789144833665697473, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_12906413484789144833665697473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369677 : Nat.totient 154876961817469738003988369677 = 151062968667434922364545452160 := by
  rw [← show ((([(41, 1), (4139, 1), (202048084387, 1), (4517028182629, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_41, prime_oneHundredThirtyOneDY_4139, prime_oneHundredThirtyOneDY_202048084387, prime_oneHundredThirtyOneDY_4517028182629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369678 : Nat.totient 154876961817469738003988369678 = 77433511177952926584994463616 := by
  rw [← show ((([(2, 1), (15913, 1), (749129, 1), (6496031953767713207, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_15913, prime_oneHundredThirtyOneDY_749129, prime_oneHundredThirtyOneDY_6496031953767713207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369679 : Nat.totient 154876961817469738003988369679 = 83687140821572067043729096704 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (557, 1), (15377, 1), (1457213, 1), (31100264197753, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_557, prime_oneHundredThirtyOneDY_15377, prime_oneHundredThirtyOneDY_1457213, prime_oneHundredThirtyOneDY_31100264197753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369680 : Nat.totient 154876961817469738003988369680 = 61950777646834288444420608000 := by
  rw [← show ((([(2, 4), (5, 1), (8749921, 1), (221254800211152960701, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_8749921, prime_oneHundredThirtyOneDY_221254800211152960701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369681 : Nat.totient 154876961817469738003988369681 = 151275168136500847904384043264 := by
  rw [← show ((([(43, 1), (58933097, 1), (116001763, 1), (526859130697, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_43, prime_oneHundredThirtyOneDY_58933097, prime_oneHundredThirtyOneDY_116001763, prime_oneHundredThirtyOneDY_526859130697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369682 : Nat.totient 154876961817469738003988369682 = 43322120925799159528693056000 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (13, 1), (632101, 1), (1151599, 1), (82659071302957, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_632101, prime_oneHundredThirtyOneDY_1151599, prime_oneHundredThirtyOneDY_82659071302957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369683 : Nat.totient 154876961817469738003988369683 = 154876961796913045275620453568 := by
  rw [← show ((([(7534138099, 1), (20556692720833778017, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_7534138099, prime_oneHundredThirtyOneDY_20556692720833778017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369684 : Nat.totient 154876961817469738003988369684 = 77436120731336334320197449024 := by
  rw [← show ((([(2, 2), (32843, 1), (33104089, 1), (35612492275348423, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_32843, prime_oneHundredThirtyOneDY_33104089, prime_oneHundredThirtyOneDY_35612492275348423]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369685 : Nat.totient 154876961817469738003988369685 = 82601046302635401654651667008 := by
  rw [← show ((([(3, 1), (5, 1), (5476990925767, 1), (1885183110173837, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_5476990925767, prime_oneHundredThirtyOneDY_1885183110173837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369686 : Nat.totient 154876961817469738003988369686 = 66375596973278927796836385600 := by
  rw [← show ((([(2, 1), (7, 1), (272249, 1), (40634272779034145213701, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_272249, prime_oneHundredThirtyOneDY_40634272779034145213701]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369687 : Nat.totient 154876961817469738003988369687 = 152695594550783624670587176920 := by
  rw [← show ((([(71, 1), (95002183, 1), (22961216158590610759, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_71, prime_oneHundredThirtyOneDY_95002183, prime_oneHundredThirtyOneDY_22961216158590610759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369688 : Nat.totient 154876961817469738003988369688 = 51397030118226172783928279040 := by
  rw [← show ((([(2, 3), (3, 1), (241, 1), (4993, 1), (13009, 1), (318077, 1), (1296047115893, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_241, prime_oneHundredThirtyOneDY_4993, prime_oneHundredThirtyOneDY_13009, prime_oneHundredThirtyOneDY_318077, prime_oneHundredThirtyOneDY_1296047115893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369689 : Nat.totient 154876961817469738003988369689 = 154869938094730342008456514800 := by
  rw [← show ((([(22051, 1), (1084721237, 1), (6475009178251847, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_22051, prime_oneHundredThirtyOneDY_1084721237, prime_oneHundredThirtyOneDY_6475009178251847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369690 : Nat.totient 154876961817469738003988369690 = 59257226914162816645959628864 := by
  rw [← show ((([(2, 1), (5, 1), (23, 1), (1304267, 1), (516288532070936455709, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_23, prime_oneHundredThirtyOneDY_1304267, prime_oneHundredThirtyOneDY_516288532070936455709]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369691 : Nat.totient 154876961817469738003988369691 = 99920620527379657983707875200 := by
  rw [← show ((([(3, 2), (31, 1), (5193896333209, 1), (106878251484581, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_31, prime_oneHundredThirtyOneDY_5193896333209, prime_oneHundredThirtyOneDY_106878251484581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369692 : Nat.totient 154876961817469738003988369692 = 72730864959102656834187340800 := by
  rw [← show ((([(2, 2), (17, 1), (743, 1), (1531, 1), (10733, 1), (186548935026342671, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_17, prime_oneHundredThirtyOneDY_743, prime_oneHundredThirtyOneDY_1531, prime_oneHundredThirtyOneDY_10733, prime_oneHundredThirtyOneDY_186548935026342671]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369693 : Nat.totient 154876961817469738003988369693 = 116208746386869571803343872000 := by
  rw [← show ((([(7, 1), (11, 1), (37, 1), (173, 1), (227, 1), (5851, 1), (236587782076245217, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_11, prime_oneHundredThirtyOneDY_37, prime_oneHundredThirtyOneDY_173, prime_oneHundredThirtyOneDY_227, prime_oneHundredThirtyOneDY_5851, prime_oneHundredThirtyOneDY_236587782076245217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369694 : Nat.totient 154876961817469738003988369694 = 51424730411169130312292997120 := by
  rw [← show ((([(2, 1), (3, 1), (257, 1), (1130287, 1), (88861515213242230411, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_257, prime_oneHundredThirtyOneDY_1130287, prime_oneHundredThirtyOneDY_88861515213242230411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369695 : Nat.totient 154876961817469738003988369695 = 110980216897946342975088672768 := by
  rw [← show ((([(5, 1), (13, 1), (53, 1), (139, 1), (263, 1), (67489, 1), (18221916511256687, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_13, prime_oneHundredThirtyOneDY_53, prime_oneHundredThirtyOneDY_139, prime_oneHundredThirtyOneDY_263, prime_oneHundredThirtyOneDY_67489, prime_oneHundredThirtyOneDY_18221916511256687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369696 : Nat.totient 154876961817469738003988369696 = 77310753730178414975076556800 := by
  rw [← show ((([(2, 5), (653, 1), (8461, 1), (875995683065771609441, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_653, prime_oneHundredThirtyOneDY_8461, prime_oneHundredThirtyOneDY_875995683065771609441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369697 : Nat.totient 154876961817469738003988369697 = 99690916889062299683046528000 := by
  rw [← show ((([(3, 1), (29, 1), (98172631, 1), (3957963721, 1), (4581475081, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_29, prime_oneHundredThirtyOneDY_98172631, prime_oneHundredThirtyOneDY_3957963721, prime_oneHundredThirtyOneDY_4581475081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369698 : Nat.totient 154876961817469738003988369698 = 73241691195903710070348230400 := by
  rw [← show ((([(2, 1), (19, 1), (613, 1), (102199, 1), (108887, 1), (6175259, 1), (96753101, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_19, prime_oneHundredThirtyOneDY_613, prime_oneHundredThirtyOneDY_102199, prime_oneHundredThirtyOneDY_108887, prime_oneHundredThirtyOneDY_6175259, prime_oneHundredThirtyOneDY_96753101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369699 : Nat.totient 154876961817469738003988369699 = 154023549679893069501508348200 := by
  rw [← show ((([(211, 1), (1291, 1), (568562383462137576602099, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_211, prime_oneHundredThirtyOneDY_1291, prime_oneHundredThirtyOneDY_568562383462137576602099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369700 : Nat.totient 154876961817469738003988369700 = 35165783328927913980283392000 := by
  rw [← show ((([(2, 2), (3, 3), (5, 2), (7, 1), (151, 1), (156493, 1), (114870583, 1), (3018869417, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2, prime_oneHundredThirtyOneDY_3, prime_oneHundredThirtyOneDY_5, prime_oneHundredThirtyOneDY_7, prime_oneHundredThirtyOneDY_151, prime_oneHundredThirtyOneDY_156493, prime_oneHundredThirtyOneDY_114870583, prime_oneHundredThirtyOneDY_3018869417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyOneDY_154876961817469738003988369701 : Nat.totient 154876961817469738003988369701 = 154810541656558799311445228160 := by
  rw [← show ((([(2333, 1), (4476631, 1), (624082649, 1), (23761763863, 1)] : List FactorBlock).map factorBlockValue).prod) = 154876961817469738003988369701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyOneDY_2333, prime_oneHundredThirtyOneDY_4476631, prime_oneHundredThirtyOneDY_624082649, prime_oneHundredThirtyOneDY_23761763863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyOneDY : certifiedKill 1 154876961817469738003988369599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyOneDY_154876961817469738003988369600, phi_oneHundredThirtyOneDY_154876961817469738003988369601, phi_oneHundredThirtyOneDY_154876961817469738003988369602,
    phi_oneHundredThirtyOneDY_154876961817469738003988369603, phi_oneHundredThirtyOneDY_154876961817469738003988369604, phi_oneHundredThirtyOneDY_154876961817469738003988369605,
    phi_oneHundredThirtyOneDY_154876961817469738003988369606, phi_oneHundredThirtyOneDY_154876961817469738003988369607, phi_oneHundredThirtyOneDY_154876961817469738003988369608,
    phi_oneHundredThirtyOneDY_154876961817469738003988369609, phi_oneHundredThirtyOneDY_154876961817469738003988369610, phi_oneHundredThirtyOneDY_154876961817469738003988369611,
    phi_oneHundredThirtyOneDY_154876961817469738003988369612, phi_oneHundredThirtyOneDY_154876961817469738003988369613, phi_oneHundredThirtyOneDY_154876961817469738003988369614,
    phi_oneHundredThirtyOneDY_154876961817469738003988369615, phi_oneHundredThirtyOneDY_154876961817469738003988369616, phi_oneHundredThirtyOneDY_154876961817469738003988369617,
    phi_oneHundredThirtyOneDY_154876961817469738003988369618, phi_oneHundredThirtyOneDY_154876961817469738003988369619, phi_oneHundredThirtyOneDY_154876961817469738003988369620,
    phi_oneHundredThirtyOneDY_154876961817469738003988369621, phi_oneHundredThirtyOneDY_154876961817469738003988369622, phi_oneHundredThirtyOneDY_154876961817469738003988369623,
    phi_oneHundredThirtyOneDY_154876961817469738003988369624, phi_oneHundredThirtyOneDY_154876961817469738003988369625, phi_oneHundredThirtyOneDY_154876961817469738003988369626,
    phi_oneHundredThirtyOneDY_154876961817469738003988369627, phi_oneHundredThirtyOneDY_154876961817469738003988369628, phi_oneHundredThirtyOneDY_154876961817469738003988369629,
    phi_oneHundredThirtyOneDY_154876961817469738003988369630, phi_oneHundredThirtyOneDY_154876961817469738003988369631, phi_oneHundredThirtyOneDY_154876961817469738003988369632,
    phi_oneHundredThirtyOneDY_154876961817469738003988369633, phi_oneHundredThirtyOneDY_154876961817469738003988369634, phi_oneHundredThirtyOneDY_154876961817469738003988369635,
    phi_oneHundredThirtyOneDY_154876961817469738003988369636, phi_oneHundredThirtyOneDY_154876961817469738003988369637, phi_oneHundredThirtyOneDY_154876961817469738003988369638,
    phi_oneHundredThirtyOneDY_154876961817469738003988369639, phi_oneHundredThirtyOneDY_154876961817469738003988369640, phi_oneHundredThirtyOneDY_154876961817469738003988369641,
    phi_oneHundredThirtyOneDY_154876961817469738003988369642, phi_oneHundredThirtyOneDY_154876961817469738003988369643, phi_oneHundredThirtyOneDY_154876961817469738003988369644,
    phi_oneHundredThirtyOneDY_154876961817469738003988369645, phi_oneHundredThirtyOneDY_154876961817469738003988369646, phi_oneHundredThirtyOneDY_154876961817469738003988369647,
    phi_oneHundredThirtyOneDY_154876961817469738003988369648, phi_oneHundredThirtyOneDY_154876961817469738003988369649, phi_oneHundredThirtyOneDY_154876961817469738003988369650,
    phi_oneHundredThirtyOneDY_154876961817469738003988369651, phi_oneHundredThirtyOneDY_154876961817469738003988369652, phi_oneHundredThirtyOneDY_154876961817469738003988369653,
    phi_oneHundredThirtyOneDY_154876961817469738003988369654, phi_oneHundredThirtyOneDY_154876961817469738003988369655, phi_oneHundredThirtyOneDY_154876961817469738003988369656,
    phi_oneHundredThirtyOneDY_154876961817469738003988369657, phi_oneHundredThirtyOneDY_154876961817469738003988369658, phi_oneHundredThirtyOneDY_154876961817469738003988369659,
    phi_oneHundredThirtyOneDY_154876961817469738003988369660, phi_oneHundredThirtyOneDY_154876961817469738003988369661, phi_oneHundredThirtyOneDY_154876961817469738003988369662,
    phi_oneHundredThirtyOneDY_154876961817469738003988369663, phi_oneHundredThirtyOneDY_154876961817469738003988369664, phi_oneHundredThirtyOneDY_154876961817469738003988369665,
    phi_oneHundredThirtyOneDY_154876961817469738003988369666, phi_oneHundredThirtyOneDY_154876961817469738003988369667, phi_oneHundredThirtyOneDY_154876961817469738003988369668,
    phi_oneHundredThirtyOneDY_154876961817469738003988369669, phi_oneHundredThirtyOneDY_154876961817469738003988369670, phi_oneHundredThirtyOneDY_154876961817469738003988369671,
    phi_oneHundredThirtyOneDY_154876961817469738003988369672, phi_oneHundredThirtyOneDY_154876961817469738003988369673, phi_oneHundredThirtyOneDY_154876961817469738003988369674,
    phi_oneHundredThirtyOneDY_154876961817469738003988369675, phi_oneHundredThirtyOneDY_154876961817469738003988369676, phi_oneHundredThirtyOneDY_154876961817469738003988369677,
    phi_oneHundredThirtyOneDY_154876961817469738003988369678, phi_oneHundredThirtyOneDY_154876961817469738003988369679, phi_oneHundredThirtyOneDY_154876961817469738003988369680,
    phi_oneHundredThirtyOneDY_154876961817469738003988369681, phi_oneHundredThirtyOneDY_154876961817469738003988369682, phi_oneHundredThirtyOneDY_154876961817469738003988369683,
    phi_oneHundredThirtyOneDY_154876961817469738003988369684, phi_oneHundredThirtyOneDY_154876961817469738003988369685, phi_oneHundredThirtyOneDY_154876961817469738003988369686,
    phi_oneHundredThirtyOneDY_154876961817469738003988369687, phi_oneHundredThirtyOneDY_154876961817469738003988369688, phi_oneHundredThirtyOneDY_154876961817469738003988369689,
    phi_oneHundredThirtyOneDY_154876961817469738003988369690, phi_oneHundredThirtyOneDY_154876961817469738003988369691, phi_oneHundredThirtyOneDY_154876961817469738003988369692,
    phi_oneHundredThirtyOneDY_154876961817469738003988369693, phi_oneHundredThirtyOneDY_154876961817469738003988369694, phi_oneHundredThirtyOneDY_154876961817469738003988369695,
    phi_oneHundredThirtyOneDY_154876961817469738003988369696, phi_oneHundredThirtyOneDY_154876961817469738003988369697, phi_oneHundredThirtyOneDY_154876961817469738003988369698,
    phi_oneHundredThirtyOneDY_154876961817469738003988369699, phi_oneHundredThirtyOneDY_154876961817469738003988369700, phi_oneHundredThirtyOneDY_154876961817469738003988369701]

end TotientTailPeriodKiller
end Erdos249257
