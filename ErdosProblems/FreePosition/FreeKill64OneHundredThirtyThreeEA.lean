import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyThreeEAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyThreeEAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyThreeEAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyThreeEAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyThreeEAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyThreeEAFastPow a n * oneHundredThirtyThreeEAFastPow a n * a else oneHundredThirtyThreeEAFastPow a n * oneHundredThirtyThreeEAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyThreeEA_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_467 : Nat.Prime 467 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_967 : Nat.Prime 967 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1031 : Nat.Prime 1031 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1123 : Nat.Prime 1123 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1301 : Nat.Prime 1301 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1619 : Nat.Prime 1619 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1741 : Nat.Prime 1741 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2027 : Nat.Prime 2027 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2087 : Nat.Prime 2087 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2273 : Nat.Prime 2273 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2293 : Nat.Prime 2293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2357 : Nat.Prime 2357 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2467 : Nat.Prime 2467 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2473 : Nat.Prime 2473 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2687 : Nat.Prime 2687 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2857 : Nat.Prime 2857 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3119 : Nat.Prime 3119 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3181 : Nat.Prime 3181 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3463 : Nat.Prime 3463 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3491 : Nat.Prime 3491 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3929 : Nat.Prime 3929 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3967 : Nat.Prime 3967 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4001 : Nat.Prime 4001 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4451 : Nat.Prime 4451 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4507 : Nat.Prime 4507 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4651 : Nat.Prime 4651 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4673 : Nat.Prime 4673 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4999 : Nat.Prime 4999 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5237 : Nat.Prime 5237 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5419 : Nat.Prime 5419 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5657 : Nat.Prime 5657 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5659 : Nat.Prime 5659 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_5903 : Nat.Prime 5903 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6091 : Nat.Prime 6091 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6547 : Nat.Prime 6547 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7079 : Nat.Prime 7079 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7451 : Nat.Prime 7451 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7643 : Nat.Prime 7643 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7817 : Nat.Prime 7817 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7937 : Nat.Prime 7937 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8123 : Nat.Prime 8123 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8293 : Nat.Prime 8293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8623 : Nat.Prime 8623 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8663 : Nat.Prime 8663 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8699 : Nat.Prime 8699 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_8807 : Nat.Prime 8807 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9091 : Nat.Prime 9091 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9227 : Nat.Prime 9227 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9283 : Nat.Prime 9283 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9343 : Nat.Prime 9343 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9851 : Nat.Prime 9851 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10223 : Nat.Prime 10223 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10243 : Nat.Prime 10243 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10267 : Nat.Prime 10267 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10531 : Nat.Prime 10531 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10667 : Nat.Prime 10667 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10799 : Nat.Prime 10799 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11287 : Nat.Prime 11287 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11491 : Nat.Prime 11491 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11497 : Nat.Prime 11497 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11617 : Nat.Prime 11617 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11777 : Nat.Prime 11777 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_11897 : Nat.Prime 11897 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_12251 : Nat.Prime 12251 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_12323 : Nat.Prime 12323 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_12697 : Nat.Prime 12697 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_13151 : Nat.Prime 13151 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_14009 : Nat.Prime 14009 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_14251 : Nat.Prime 14251 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_15361 : Nat.Prime 15361 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_15581 : Nat.Prime 15581 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_16421 : Nat.Prime 16421 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17293 : Nat.Prime 17293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_18481 : Nat.Prime 18481 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_19403 : Nat.Prime 19403 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_21031 : Nat.Prime 21031 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_21247 : Nat.Prime 21247 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_21517 : Nat.Prime 21517 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_21661 : Nat.Prime 21661 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_22027 : Nat.Prime 22027 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_23321 : Nat.Prime 23321 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_24631 : Nat.Prime 24631 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_25411 : Nat.Prime 25411 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_25747 : Nat.Prime 25747 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_27763 : Nat.Prime 27763 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28307 : Nat.Prime 28307 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28591 : Nat.Prime 28591 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_29077 : Nat.Prime 29077 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_32561 : Nat.Prime 32561 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_35951 : Nat.Prime 35951 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_37991 : Nat.Prime 37991 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_40771 : Nat.Prime 40771 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_41149 : Nat.Prime 41149 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_42953 : Nat.Prime 42953 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_44507 : Nat.Prime 44507 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_46447 : Nat.Prime 46447 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_46957 : Nat.Prime 46957 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_47659 : Nat.Prime 47659 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_48271 : Nat.Prime 48271 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_48479 : Nat.Prime 48479 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_48991 : Nat.Prime 48991 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_49613 : Nat.Prime 49613 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_54419 : Nat.Prime 54419 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_54833 : Nat.Prime 54833 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_55901 : Nat.Prime 55901 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_56659 : Nat.Prime 56659 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_57367 : Nat.Prime 57367 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_59417 : Nat.Prime 59417 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_60821 : Nat.Prime 60821 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_63211 : Nat.Prime 63211 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_66457 : Nat.Prime 66457 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_68711 : Nat.Prime 68711 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_74197 : Nat.Prime 74197 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_75991 : Nat.Prime 75991 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_76511 : Nat.Prime 76511 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_76717 : Nat.Prime 76717 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_78031 : Nat.Prime 78031 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_79687 : Nat.Prime 79687 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_80917 : Nat.Prime 80917 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_85303 : Nat.Prime 85303 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_88663 : Nat.Prime 88663 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_89597 : Nat.Prime 89597 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_90089 : Nat.Prime 90089 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_90397 : Nat.Prime 90397 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_95917 : Nat.Prime 95917 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_99119 : Nat.Prime 99119 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_103687 : Nat.Prime 103687 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_103889 : Nat.Prime 103889 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_104107 : Nat.Prime 104107 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_106243 : Nat.Prime 106243 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_109793 : Nat.Prime 109793 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_110951 : Nat.Prime 110951 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_111791 : Nat.Prime 111791 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_125471 : Nat.Prime 125471 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_126713 : Nat.Prime 126713 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_143141 : Nat.Prime 143141 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_143401 : Nat.Prime 143401 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_143527 : Nat.Prime 143527 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_145637 : Nat.Prime 145637 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_150767 : Nat.Prime 150767 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_150979 : Nat.Prime 150979 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_154291 : Nat.Prime 154291 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_157837 : Nat.Prime 157837 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_161267 : Nat.Prime 161267 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_164821 : Nat.Prime 164821 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_166259 : Nat.Prime 166259 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_171023 : Nat.Prime 171023 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_186113 : Nat.Prime 186113 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_201451 : Nat.Prime 201451 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_205559 : Nat.Prime 205559 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_205993 : Nat.Prime 205993 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_212453 : Nat.Prime 212453 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_212909 : Nat.Prime 212909 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_215309 : Nat.Prime 215309 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_231571 : Nat.Prime 231571 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_233117 : Nat.Prime 233117 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_242813 : Nat.Prime 242813 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_283277 : Nat.Prime 283277 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_283487 : Nat.Prime 283487 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_299281 : Nat.Prime 299281 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_305411 : Nat.Prime 305411 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_317021 : Nat.Prime 317021 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_323053 : Nat.Prime 323053 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_324161 : Nat.Prime 324161 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_336533 : Nat.Prime 336533 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_344293 : Nat.Prime 344293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_352333 : Nat.Prime 352333 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_378011 : Nat.Prime 378011 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_383767 : Nat.Prime 383767 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_387493 : Nat.Prime 387493 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_417187 : Nat.Prime 417187 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_420757 : Nat.Prime 420757 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_422701 : Nat.Prime 422701 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_429281 : Nat.Prime 429281 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_453833 : Nat.Prime 453833 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_502409 : Nat.Prime 502409 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_506729 : Nat.Prime 506729 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_526387 : Nat.Prime 526387 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_551569 : Nat.Prime 551569 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_594119 : Nat.Prime 594119 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_602081 : Nat.Prime 602081 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_618997 : Nat.Prime 618997 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_670493 : Nat.Prime 670493 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_699493 : Nat.Prime 699493 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_718841 : Nat.Prime 718841 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_809771 : Nat.Prime 809771 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_827227 : Nat.Prime 827227 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_837667 : Nat.Prime 837667 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_862307 : Nat.Prime 862307 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_882157 : Nat.Prime 882157 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_897059 : Nat.Prime 897059 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_902953 : Nat.Prime 902953 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_982067 : Nat.Prime 982067 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_984911 : Nat.Prime 984911 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1007971 : Nat.Prime 1007971 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1066973 : Nat.Prime 1066973 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1172537 : Nat.Prime 1172537 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1184527 : Nat.Prime 1184527 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1187189 : Nat.Prime 1187189 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1284341 : Nat.Prime 1284341 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1348379 : Nat.Prime 1348379 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1416809 : Nat.Prime 1416809 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1436249 : Nat.Prime 1436249 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1496927 : Nat.Prime 1496927 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1630933 : Nat.Prime 1630933 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1631573 : Nat.Prime 1631573 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1677349 : Nat.Prime 1677349 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1703297 : Nat.Prime 1703297 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1708409 : Nat.Prime 1708409 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1768157 : Nat.Prime 1768157 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1815599 : Nat.Prime 1815599 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_1992257 : Nat.Prime 1992257 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2053189 : Nat.Prime 2053189 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2115703 : Nat.Prime 2115703 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2261549 : Nat.Prime 2261549 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2275657 : Nat.Prime 2275657 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2453921 : Nat.Prime 2453921 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2507927 : Nat.Prime 2507927 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2718137 : Nat.Prime 2718137 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2734579 : Nat.Prime 2734579 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2761553 : Nat.Prime 2761553 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2817043 : Nat.Prime 2817043 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2857949 : Nat.Prime 2857949 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2941571 : Nat.Prime 2941571 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_2977087 : Nat.Prime 2977087 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3101591 : Nat.Prime 3101591 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3481117 : Nat.Prime 3481117 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3593003 : Nat.Prime 3593003 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3605759 : Nat.Prime 3605759 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_3751901 : Nat.Prime 3751901 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4154819 : Nat.Prime 4154819 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4524017 : Nat.Prime 4524017 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4558633 : Nat.Prime 4558633 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_4854653 : Nat.Prime 4854653 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6116111 : Nat.Prime 6116111 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6465527 : Nat.Prime 6465527 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6496283 : Nat.Prime 6496283 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6500887 : Nat.Prime 6500887 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6647743 : Nat.Prime 6647743 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_6830777 : Nat.Prime 6830777 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7125553 : Nat.Prime 7125553 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_7702571 : Nat.Prime 7702571 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9489517 : Nat.Prime 9489517 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9552197 : Nat.Prime 9552197 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9664903 : Nat.Prime 9664903 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_9917909 : Nat.Prime 9917909 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10233161 : Nat.Prime 10233161 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10361777 : Nat.Prime 10361777 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10708471 : Nat.Prime 10708471 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10819147 : Nat.Prime 10819147 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_13829869 : Nat.Prime 13829869 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_15117469 : Nat.Prime 15117469 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_15930221 : Nat.Prime 15930221 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_16813801 : Nat.Prime 16813801 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_16871527 : Nat.Prime 16871527 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_17609173 : Nat.Prime 17609173 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_19001417 : Nat.Prime 19001417 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_20476153 : Nat.Prime 20476153 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_22269101 : Nat.Prime 22269101 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_22297057 : Nat.Prime 22297057 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_23809811 : Nat.Prime 23809811 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_24175577 : Nat.Prime 24175577 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28125473 : Nat.Prime 28125473 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28458863 : Nat.Prime 28458863 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28581281 : Nat.Prime 28581281 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_28901293 : Nat.Prime 28901293 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_29835101 : Nat.Prime 29835101 := by norm_num

private theorem prime_oneHundredThirtyThreeEA_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_73
      · exact prime_oneHundredThirtyThreeEA_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_33450281 : Nat.Prime 33450281 := by
  apply lucas_primality 33450281 (6 : ZMod 33450281)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (23, 1), (103, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (23, 1), (103, 1), (353, 1)] : List FactorBlock).map factorBlockValue).prod) = 33450281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_103
      · exact prime_oneHundredThirtyThreeEA_353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33450281) ^ 16725140 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33450281) ^ 6690056 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33450281) ^ 1454360 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33450281) ^ 324760 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 33450281) ^ 94760 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_34794311 : Nat.Prime 34794311 := by
  apply lucas_primality 34794311 (13 : ZMod 34794311)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (80917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (80917, 1)] : List FactorBlock).map factorBlockValue).prod) = 34794311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_43
      · exact prime_oneHundredThirtyThreeEA_80917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 34794311) ^ 17397155 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 34794311) ^ 6958862 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 34794311) ^ 809170 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 34794311) ^ 430 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_35298853 : Nat.Prime 35298853 := by
  apply lucas_primality 35298853 (2 : ZMod 35298853)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2941571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2941571, 1)] : List FactorBlock).map factorBlockValue).prod) = 35298853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_2941571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35298853) ^ 17649426 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35298853) ^ 11766284 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35298853) ^ 12 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_36074099 : Nat.Prime 36074099 := by
  apply lucas_primality 36074099 (2 : ZMod 36074099)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (383767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (383767, 1)] : List FactorBlock).map factorBlockValue).prod) = 36074099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_383767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 36074099) ^ 18037049 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36074099) ^ 767534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36074099) ^ 94 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_38053919 : Nat.Prime 38053919 := by
  apply lucas_primality 38053919 (7 : ZMod 38053919)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2718137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2718137, 1)] : List FactorBlock).map factorBlockValue).prod) = 38053919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_2718137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 38053919) ^ 19026959 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 38053919) ^ 5436274 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 38053919) ^ 14 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_40822129 : Nat.Prime 40822129 := by
  apply lucas_primality 40822129 (7 : ZMod 40822129)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (283487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (283487, 1)] : List FactorBlock).map factorBlockValue).prod) = 40822129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_283487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 40822129) ^ 20411064 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 40822129) ^ 13607376 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 40822129) ^ 144 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_41210977 : Nat.Prime 41210977 := by
  apply lucas_primality 41210977 (5 : ZMod 41210977)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (429281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (429281, 1)] : List FactorBlock).map factorBlockValue).prod) = 41210977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_429281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 41210977) ^ 20605488 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 41210977) ^ 13736992 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 41210977) ^ 96 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_44959949 : Nat.Prime 44959949 := by
  apply lucas_primality 44959949 (3 : ZMod 44959949)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (67, 1), (101, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (67, 1), (101, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 44959949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_67
      · exact prime_oneHundredThirtyThreeEA_101
      · exact prime_oneHundredThirtyThreeEA_151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 44959949) ^ 22479974 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 44959949) ^ 4087268 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 44959949) ^ 671044 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 44959949) ^ 445148 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 44959949) ^ 297748 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_47275729 : Nat.Prime 47275729 := by
  apply lucas_primality 47275729 (11 : ZMod 47275729)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (984911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (984911, 1)] : List FactorBlock).map factorBlockValue).prod) = 47275729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_984911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 47275729) ^ 23637864 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 47275729) ^ 15758576 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 47275729) ^ 48 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_47619623 : Nat.Prime 47619623 := by
  apply lucas_primality 47619623 (5 : ZMod 47619623)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23809811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23809811, 1)] : List FactorBlock).map factorBlockValue).prod) = 47619623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_23809811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 47619623) ^ 23809811 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 47619623) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_56069599 : Nat.Prime 56069599 := by
  apply lucas_primality 56069599 (15 : ZMod 56069599)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) = 56069599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_718841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 56069599) ^ 28034799 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 18689866 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 4313046 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 78 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_56917727 : Nat.Prime 56917727 := by
  apply lucas_primality 56917727 (5 : ZMod 56917727)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (28458863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (28458863, 1)] : List FactorBlock).map factorBlockValue).prod) = 56917727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_28458863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 56917727) ^ 28458863 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56917727) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_57371477 : Nat.Prime 57371477 := by
  apply lucas_primality 57371477 (3 : ZMod 57371477)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (61, 1), (10223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (61, 1), (10223, 1)] : List FactorBlock).map factorBlockValue).prod) = 57371477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_10223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 57371477) ^ 28685738 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57371477) ^ 2494412 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57371477) ^ 940516 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57371477) ^ 5612 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_57404539 : Nat.Prime 57404539 := by
  apply lucas_primality 57404539 (3 : ZMod 57404539)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (37, 1), (61, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (37, 1), (61, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 57404539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 57404539) ^ 28702269 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57404539) ^ 19134846 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57404539) ^ 1551474 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57404539) ^ 941058 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 57404539) ^ 365634 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_66900563 : Nat.Prime 66900563 := by
  apply lucas_primality 66900563 (2 : ZMod 66900563)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (33450281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (33450281, 1)] : List FactorBlock).map factorBlockValue).prod) = 66900563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_33450281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66900563) ^ 33450281 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66900563) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_67534219 : Nat.Prime 67534219 := by
  apply lucas_primality 67534219 (2 : ZMod 67534219)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3751901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3751901, 1)] : List FactorBlock).map factorBlockValue).prod) = 67534219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_3751901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 67534219) ^ 33767109 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67534219) ^ 22511406 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67534219) ^ 18 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_68984561 : Nat.Prime 68984561 := by
  apply lucas_primality 68984561 (3 : ZMod 68984561)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (862307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (862307, 1)] : List FactorBlock).map factorBlockValue).prod) = 68984561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_862307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68984561) ^ 34492280 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 68984561) ^ 13796912 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 68984561) ^ 80 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_69607949 : Nat.Prime 69607949 := by
  apply lucas_primality 69607949 (2 : ZMod 69607949)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2857, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2857, 1), (6091, 1)] : List FactorBlock).map factorBlockValue).prod) = 69607949 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2857
      · exact prime_oneHundredThirtyThreeEA_6091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 69607949) ^ 34803974 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 69607949) ^ 24364 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 69607949) ^ 11428 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_72148199 : Nat.Prime 72148199 := by
  apply lucas_primality 72148199 (7 : ZMod 72148199)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (36074099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (36074099, 1)] : List FactorBlock).map factorBlockValue).prod) = 72148199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_36074099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 72148199) ^ 36074099 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 72148199) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_72438131 : Nat.Prime 72438131 := by
  apply lucas_primality 72438131 (2 : ZMod 72438131)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (109, 1), (66457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (109, 1), (66457, 1)] : List FactorBlock).map factorBlockValue).prod) = 72438131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_109
      · exact prime_oneHundredThirtyThreeEA_66457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 72438131) ^ 36219065 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72438131) ^ 14487626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72438131) ^ 664570 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 72438131) ^ 1090 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_85992383 : Nat.Prime 85992383 := by
  apply lucas_primality 85992383 (5 : ZMod 85992383)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (104107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (104107, 1)] : List FactorBlock).map factorBlockValue).prod) = 85992383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_59
      · exact prime_oneHundredThirtyThreeEA_104107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 85992383) ^ 42996191 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85992383) ^ 12284626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85992383) ^ 1457498 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85992383) ^ 826 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_91454369 : Nat.Prime 91454369 := by
  apply lucas_primality 91454369 (3 : ZMod 91454369)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) = 91454369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2857949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 91454369) ^ 45727184 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 91454369) ^ 32 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_91686379 : Nat.Prime 91686379 := by
  apply lucas_primality 91686379 (2 : ZMod 91686379)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (47, 1), (46447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (47, 1), (46447, 1)] : List FactorBlock).map factorBlockValue).prod) = 91686379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_46447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91686379) ^ 45843189 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 91686379) ^ 30562126 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 91686379) ^ 13098054 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 91686379) ^ 1950774 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 91686379) ^ 1974 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_95239247 : Nat.Prime 95239247 := by
  apply lucas_primality 95239247 (5 : ZMod 95239247)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47619623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47619623, 1)] : List FactorBlock).map factorBlockValue).prod) = 95239247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_47619623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 95239247) ^ 47619623 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 95239247) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_99715657 : Nat.Prime 99715657 := by
  apply lucas_primality 99715657 (10 : ZMod 99715657)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (4154819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (4154819, 1)] : List FactorBlock).map factorBlockValue).prod) = 99715657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_4154819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 99715657) ^ 49857828 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 99715657) ^ 33238552 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 99715657) ^ 24 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_101080961 : Nat.Prime 101080961 := by
  apply lucas_primality 101080961 (3 : ZMod 101080961)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 101080961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_43
      · exact prime_oneHundredThirtyThreeEA_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101080961) ^ 50540480 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 20216192 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 2350720 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 27520 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_102845747 : Nat.Prime 102845747 := by
  apply lucas_primality 102845747 (2 : ZMod 102845747)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (257, 1), (10531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (257, 1), (10531, 1)] : List FactorBlock).map factorBlockValue).prod) = 102845747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_257
      · exact prime_oneHundredThirtyThreeEA_10531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102845747) ^ 51422873 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102845747) ^ 5412934 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102845747) ^ 400178 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 102845747) ^ 9766 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_104230603 : Nat.Prime 104230603 := by
  apply lucas_primality 104230603 (2 : ZMod 104230603)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (827227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (827227, 1)] : List FactorBlock).map factorBlockValue).prod) = 104230603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_827227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 104230603) ^ 52115301 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 104230603) ^ 34743534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 104230603) ^ 14890086 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 104230603) ^ 126 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_117021139 : Nat.Prime 117021139 := by
  apply lucas_primality 117021139 (11 : ZMod 117021139)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (53, 1), (28307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (53, 1), (28307, 1)] : List FactorBlock).map factorBlockValue).prod) = 117021139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_28307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 117021139) ^ 58510569 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 117021139) ^ 39007046 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 117021139) ^ 9001626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 117021139) ^ 2207946 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 117021139) ^ 4134 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_124375177 : Nat.Prime 124375177 := by
  apply lucas_primality 124375177 (5 : ZMod 124375177)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 5), (137, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 5), (137, 1), (467, 1)] : List FactorBlock).map factorBlockValue).prod) = 124375177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_137
      · exact prime_oneHundredThirtyThreeEA_467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 124375177) ^ 62187588 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 41458392 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 907848 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 124375177) ^ 266328 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_125933891 : Nat.Prime 125933891 := by
  apply lucas_primality 125933891 (2 : ZMod 125933891)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 125933891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_431
      · exact prime_oneHundredThirtyThreeEA_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125933891) ^ 62966945 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 25186778 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 2064490 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 292190 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 262910 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_141343861 : Nat.Prime 141343861 := by
  apply lucas_primality 141343861 (2 : ZMod 141343861)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (336533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (336533, 1)] : List FactorBlock).map factorBlockValue).prod) = 141343861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_336533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 141343861) ^ 70671930 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141343861) ^ 47114620 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141343861) ^ 28268772 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141343861) ^ 20191980 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141343861) ^ 420 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_147829609 : Nat.Prime 147829609 := by
  apply lucas_primality 147829609 (17 : ZMod 147829609)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (2053189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (2053189, 1)] : List FactorBlock).map factorBlockValue).prod) = 147829609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_2053189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 147829609) ^ 73914804 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 147829609) ^ 49276536 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 147829609) ^ 72 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_150655151 : Nat.Prime 150655151 := by
  apply lucas_primality 150655151 (11 : ZMod 150655151)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (53, 1), (139, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (53, 1), (139, 1), (409, 1)] : List FactorBlock).map factorBlockValue).prod) = 150655151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_139
      · exact prime_oneHundredThirtyThreeEA_409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 150655151) ^ 75327575 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 150655151) ^ 30131030 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 150655151) ^ 2842550 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 150655151) ^ 1083850 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 150655151) ^ 368350 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_156021289 : Nat.Prime 156021289 := by
  apply lucas_primality 156021289 (11 : ZMod 156021289)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (6500887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (6500887, 1)] : List FactorBlock).map factorBlockValue).prod) = 156021289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_6500887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 156021289) ^ 78010644 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 156021289) ^ 52007096 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 156021289) ^ 24 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_159339751 : Nat.Prime 159339751 := by
  apply lucas_primality 159339751 (3 : ZMod 159339751)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (212453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (212453, 1)] : List FactorBlock).map factorBlockValue).prod) = 159339751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_212453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 159339751) ^ 79669875 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 159339751) ^ 53113250 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 159339751) ^ 31867950 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 159339751) ^ 750 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_174411121 : Nat.Prime 174411121 := by
  apply lucas_primality 174411121 (7 : ZMod 174411121)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (13, 1), (55901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (13, 1), (55901, 1)] : List FactorBlock).map factorBlockValue).prod) = 174411121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_55901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 174411121) ^ 87205560 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 174411121) ^ 58137040 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 174411121) ^ 34882224 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 174411121) ^ 13416240 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 174411121) ^ 3120 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_187568509 : Nat.Prime 187568509 := by
  apply lucas_primality 187568509 (10 : ZMod 187568509)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (109, 1), (143401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (109, 1), (143401, 1)] : List FactorBlock).map factorBlockValue).prod) = 187568509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_109
      · exact prime_oneHundredThirtyThreeEA_143401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 187568509) ^ 93784254 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 187568509) ^ 62522836 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 187568509) ^ 1720812 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 187568509) ^ 1308 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_193897349 : Nat.Prime 193897349 := by
  apply lucas_primality 193897349 (2 : ZMod 193897349)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) = 193897349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_797
      · exact prime_oneHundredThirtyThreeEA_60821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 193897349) ^ 96948674 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 243284 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 3188 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_204185141 : Nat.Prime 204185141 := by
  apply lucas_primality 204185141 (2 : ZMod 204185141)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (99119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (99119, 1)] : List FactorBlock).map factorBlockValue).prod) = 204185141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_103
      · exact prime_oneHundredThirtyThreeEA_99119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 204185141) ^ 102092570 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 204185141) ^ 40837028 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 204185141) ^ 1982380 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 204185141) ^ 2060 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_224075651 : Nat.Prime 224075651 := by
  apply lucas_primality 224075651 (2 : ZMod 224075651)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (827, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (827, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) = 224075651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_827
      · exact prime_oneHundredThirtyThreeEA_5419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224075651) ^ 112037825 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 224075651) ^ 44815130 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 224075651) ^ 270950 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 224075651) ^ 41350 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_225980453 : Nat.Prime 225980453 := by
  apply lucas_primality 225980453 (2 : ZMod 225980453)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (31, 1), (95917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (31, 1), (95917, 1)] : List FactorBlock).map factorBlockValue).prod) = 225980453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_95917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 225980453) ^ 112990226 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 225980453) ^ 11893708 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 225980453) ^ 7289692 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 225980453) ^ 2356 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_258026507 : Nat.Prime 258026507 := by
  apply lucas_primality 258026507 (2 : ZMod 258026507)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1619, 1), (79687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1619, 1), (79687, 1)] : List FactorBlock).map factorBlockValue).prod) = 258026507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1619
      · exact prime_oneHundredThirtyThreeEA_79687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 258026507) ^ 129013253 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 258026507) ^ 159374 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 258026507) ^ 3238 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_258170491 : Nat.Prime 258170491 := by
  apply lucas_primality 258170491 (10 : ZMod 258170491)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (106243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (106243, 1)] : List FactorBlock).map factorBlockValue).prod) = 258170491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_106243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 258170491) ^ 129085245 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 258170491) ^ 86056830 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 258170491) ^ 51634098 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 258170491) ^ 2430 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_334187233 : Nat.Prime 334187233 := by
  apply lucas_primality 334187233 (11 : ZMod 334187233)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (3481117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (3481117, 1)] : List FactorBlock).map factorBlockValue).prod) = 334187233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_3481117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 334187233) ^ 167093616 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 334187233) ^ 111395744 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 334187233) ^ 96 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_335612729 : Nat.Prime 335612729 := by
  apply lucas_primality 335612729 (3 : ZMod 335612729)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (61, 1), (103, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (61, 1), (103, 1), (607, 1)] : List FactorBlock).map factorBlockValue).prod) = 335612729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_103
      · exact prime_oneHundredThirtyThreeEA_607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335612729) ^ 167806364 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335612729) ^ 30510248 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335612729) ^ 5501848 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335612729) ^ 3258376 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335612729) ^ 552904 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_349370653 : Nat.Prime 349370653 := by
  apply lucas_primality 349370653 (2 : ZMod 349370653)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2293, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2293, 1), (12697, 1)] : List FactorBlock).map factorBlockValue).prod) = 349370653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_2293
      · exact prime_oneHundredThirtyThreeEA_12697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 349370653) ^ 174685326 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 349370653) ^ 116456884 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 349370653) ^ 152364 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 349370653) ^ 27516 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_359488603 : Nat.Prime 359488603 := by
  apply lucas_primality 359488603 (3 : ZMod 359488603)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (1815599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (1815599, 1)] : List FactorBlock).map factorBlockValue).prod) = 359488603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_1815599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 359488603) ^ 179744301 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 359488603) ^ 119829534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 359488603) ^ 32680782 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 359488603) ^ 198 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_383238773 : Nat.Prime 383238773 := by
  apply lucas_primality 383238773 (2 : ZMod 383238773)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2357, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2357, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) = 383238773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_2357
      · exact prime_oneHundredThirtyThreeEA_5807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 383238773) ^ 191619386 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 383238773) ^ 54748396 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 383238773) ^ 162596 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 383238773) ^ 65996 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_417531733 : Nat.Prime 417531733 := by
  apply lucas_primality 417531733 (5 : ZMod 417531733)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (34794311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (34794311, 1)] : List FactorBlock).map factorBlockValue).prod) = 417531733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_34794311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 417531733) ^ 208765866 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417531733) ^ 139177244 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 417531733) ^ 12 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_448151303 : Nat.Prime 448151303 := by
  apply lucas_primality 448151303 (5 : ZMod 448151303)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (224075651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (224075651, 1)] : List FactorBlock).map factorBlockValue).prod) = 448151303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_224075651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 448151303) ^ 224075651 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 448151303) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_648508079 : Nat.Prime 648508079 := by
  apply lucas_primality 648508079 (7 : ZMod 648508079)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (211, 1), (90397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (211, 1), (90397, 1)] : List FactorBlock).map factorBlockValue).prod) = 648508079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_211
      · exact prime_oneHundredThirtyThreeEA_90397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 648508079) ^ 324254039 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 648508079) ^ 38147534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 648508079) ^ 3073498 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 648508079) ^ 7174 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17203
      · exact prime_oneHundredThirtyThreeEA_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_101
      · exact prime_oneHundredThirtyThreeEA_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_754786177 : Nat.Prime 754786177 := by
  apply lucas_primality 754786177 (10 : ZMod 754786177)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (1129, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (1129, 1), (1741, 1)] : List FactorBlock).map factorBlockValue).prod) = 754786177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_1129
      · exact prime_oneHundredThirtyThreeEA_1741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 754786177) ^ 377393088 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 754786177) ^ 251595392 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 754786177) ^ 668544 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 754786177) ^ 433536 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_762026077 : Nat.Prime 762026077 := by
  apply lucas_primality 762026077 (2 : ZMod 762026077)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (1007971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (1007971, 1)] : List FactorBlock).map factorBlockValue).prod) = 762026077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_1007971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 762026077) ^ 381013038 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 762026077) ^ 254008692 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 762026077) ^ 108860868 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 762026077) ^ 756 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_869257573 : Nat.Prime 869257573 := by
  apply lucas_primality 869257573 (2 : ZMod 869257573)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (72438131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (72438131, 1)] : List FactorBlock).map factorBlockValue).prod) = 869257573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_72438131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 869257573) ^ 434628786 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 869257573) ^ 289752524 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 869257573) ^ 12 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_896642093 : Nat.Prime 896642093 := by
  apply lucas_primality 896642093 (2 : ZMod 896642093)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) = 896642093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_593
      · exact prime_oneHundredThirtyThreeEA_378011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 896642093) ^ 448321046 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 1512044 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 2372 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_956038507 : Nat.Prime 956038507 := by
  apply lucas_primality 956038507 (2 : ZMod 956038507)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (159339751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (159339751, 1)] : List FactorBlock).map factorBlockValue).prod) = 956038507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_159339751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 956038507) ^ 478019253 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 956038507) ^ 318679502 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 956038507) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_974344927 : Nat.Prime 974344927 := by
  apply lucas_primality 974344927 (3 : ZMod 974344927)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7643, 1), (21247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7643, 1), (21247, 1)] : List FactorBlock).map factorBlockValue).prod) = 974344927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7643
      · exact prime_oneHundredThirtyThreeEA_21247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 974344927) ^ 487172463 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 974344927) ^ 324781642 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 974344927) ^ 127482 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 974344927) ^ 45858 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1140155257 : Nat.Prime 1140155257 := by
  apply lucas_primality 1140155257 (5 : ZMod 1140155257)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (3049, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (3049, 1), (15581, 1)] : List FactorBlock).map factorBlockValue).prod) = 1140155257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_3049
      · exact prime_oneHundredThirtyThreeEA_15581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1140155257) ^ 570077628 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140155257) ^ 380051752 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140155257) ^ 373944 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1140155257) ^ 73176 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1205241209 : Nat.Prime 1205241209 := by
  apply lucas_primality 1205241209 (3 : ZMod 1205241209)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (150655151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (150655151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205241209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_150655151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1205241209) ^ 602620604 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1205241209) ^ 8 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1601997113 : Nat.Prime 1601997113 := by
  apply lucas_primality 1601997113 (3 : ZMod 1601997113)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (227, 1), (882157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (227, 1), (882157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1601997113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_227
      · exact prime_oneHundredThirtyThreeEA_882157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1601997113) ^ 800998556 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1601997113) ^ 7057256 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1601997113) ^ 1816 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1659584281 : Nat.Prime 1659584281 := by
  apply lucas_primality 1659584281 (19 : ZMod 1659584281)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13829869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13829869, 1)] : List FactorBlock).map factorBlockValue).prod) = 1659584281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13829869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 1659584281) ^ 829792140 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659584281) ^ 553194760 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659584281) ^ 331916856 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 1659584281) ^ 120 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1890247399 : Nat.Prime 1890247399 := by
  apply lucas_primality 1890247399 (6 : ZMod 1890247399)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (269, 1), (90089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (269, 1), (90089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1890247399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_269
      · exact prime_oneHundredThirtyThreeEA_90089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1890247399) ^ 945123699 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1890247399) ^ 630082466 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1890247399) ^ 145403646 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1890247399) ^ 7026942 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 1890247399) ^ 20982 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1910495123 : Nat.Prime 1910495123 := by
  apply lucas_primality 1910495123 (2 : ZMod 1910495123)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (41, 1), (71, 1), (97, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (41, 1), (71, 1), (97, 1), (199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1910495123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_41
      · exact prime_oneHundredThirtyThreeEA_71
      · exact prime_oneHundredThirtyThreeEA_97
      · exact prime_oneHundredThirtyThreeEA_199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1910495123) ^ 955247561 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1910495123) ^ 112382066 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1910495123) ^ 46597442 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1910495123) ^ 26908382 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1910495123) ^ 19695826 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1910495123) ^ 9600478 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1975441217 : Nat.Prime 1975441217 := by
  apply lucas_primality 1975441217 (3 : ZMod 1975441217)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (509, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (509, 1), (8663, 1)] : List FactorBlock).map factorBlockValue).prod) = 1975441217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_509
      · exact prime_oneHundredThirtyThreeEA_8663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1975441217) ^ 987720608 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1975441217) ^ 282205888 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1975441217) ^ 3881024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1975441217) ^ 228032 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2111892553 : Nat.Prime 2111892553 := by
  apply lucas_primality 2111892553 (17 : ZMod 2111892553)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (11, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (11, 1), (54419, 1)] : List FactorBlock).map factorBlockValue).prod) = 2111892553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_54419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2111892553) ^ 1055946276 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2111892553) ^ 703964184 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2111892553) ^ 301698936 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2111892553) ^ 191990232 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2111892553) ^ 38808 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2138438371 : Nat.Prime 2138438371 := by
  apply lucas_primality 2138438371 (10 : ZMod 2138438371)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (383, 1), (186113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (383, 1), (186113, 1)] : List FactorBlock).map factorBlockValue).prod) = 2138438371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_383
      · exact prime_oneHundredThirtyThreeEA_186113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2138438371) ^ 1069219185 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2138438371) ^ 712812790 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2138438371) ^ 427687674 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2138438371) ^ 5583390 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2138438371) ^ 11490 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2273528107 : Nat.Prime 2273528107 := by
  apply lucas_primality 2273528107 (3 : ZMod 2273528107)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (6647743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (6647743, 1)] : List FactorBlock).map factorBlockValue).prod) = 2273528107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_6647743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2273528107) ^ 1136764053 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2273528107) ^ 757842702 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2273528107) ^ 119659374 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2273528107) ^ 342 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2505190399 : Nat.Prime 2505190399 := by
  apply lucas_primality 2505190399 (3 : ZMod 2505190399)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (417531733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (417531733, 1)] : List FactorBlock).map factorBlockValue).prod) = 2505190399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_417531733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2505190399) ^ 1252595199 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505190399) ^ 835063466 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2505190399) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2551471159 : Nat.Prime 2551471159 := by
  apply lucas_primality 2551471159 (6 : ZMod 2551471159)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (359, 1), (1184527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (359, 1), (1184527, 1)] : List FactorBlock).map factorBlockValue).prod) = 2551471159 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_359
      · exact prime_oneHundredThirtyThreeEA_1184527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 2551471159) ^ 1275735579 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2551471159) ^ 850490386 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2551471159) ^ 7107162 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2551471159) ^ 2154 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2684901833 : Nat.Prime 2684901833 := by
  apply lucas_primality 2684901833 (3 : ZMod 2684901833)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (335612729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (335612729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2684901833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_335612729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 2684901833) ^ 1342450916 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2684901833) ^ 8 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2864331863 : Nat.Prime 2864331863 := by
  apply lucas_primality 2864331863 (5 : ZMod 2864331863)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (283, 1), (23321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (283, 1), (23321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2864331863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_283
      · exact prime_oneHundredThirtyThreeEA_23321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2864331863) ^ 1432165931 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2864331863) ^ 409190266 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2864331863) ^ 92397802 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2864331863) ^ 10121314 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2864331863) ^ 122822 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2877395683 : Nat.Prime 2877395683 := by
  apply lucas_primality 2877395683 (17 : ZMod 2877395683)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (19, 1), (3605759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (19, 1), (3605759, 1)] : List FactorBlock).map factorBlockValue).prod) = 2877395683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_3605759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 2877395683) ^ 1438697841 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2877395683) ^ 959131894 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2877395683) ^ 411056526 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2877395683) ^ 151441878 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 2877395683) ^ 798 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2994083123 : Nat.Prime 2994083123 := by
  apply lucas_primality 2994083123 (2 : ZMod 2994083123)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9283, 1), (161267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9283, 1), (161267, 1)] : List FactorBlock).map factorBlockValue).prod) = 2994083123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_9283
      · exact prime_oneHundredThirtyThreeEA_161267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2994083123) ^ 1497041561 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2994083123) ^ 322534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2994083123) ^ 18566 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3085062853 : Nat.Prime 3085062853 := by
  apply lucas_primality 3085062853 (2 : ZMod 3085062853)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (1436249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (1436249, 1)] : List FactorBlock).map factorBlockValue).prod) = 3085062853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_179
      · exact prime_oneHundredThirtyThreeEA_1436249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3085062853) ^ 1542531426 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3085062853) ^ 1028354284 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3085062853) ^ 17234988 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3085062853) ^ 2148 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3170511431 : Nat.Prime 3170511431 := by
  apply lucas_primality 3170511431 (17 : ZMod 3170511431)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 2), (143527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 2), (143527, 1)] : List FactorBlock).map factorBlockValue).prod) = 3170511431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_143527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 3170511431) ^ 1585255715 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 3170511431) ^ 634102286 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 3170511431) ^ 67457690 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 3170511431) ^ 22090 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3432468359 : Nat.Prime 3432468359 := by
  apply lucas_primality 3432468359 (11 : ZMod 3432468359)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (156021289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (156021289, 1)] : List FactorBlock).map factorBlockValue).prod) = 3432468359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_156021289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 3432468359) ^ 1716234179 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3432468359) ^ 312042578 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 3432468359) ^ 22 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3515265851 : Nat.Prime 3515265851 := by
  apply lucas_primality 3515265851 (2 : ZMod 3515265851)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3515265851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_4783
      · exact prime_oneHundredThirtyThreeEA_14699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3515265851) ^ 1757632925 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 703053170 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 734950 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 239150 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4469320301 : Nat.Prime 4469320301 := by
  apply lucas_primality 4469320301 (2 : ZMod 4469320301)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (193, 1), (231571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (193, 1), (231571, 1)] : List FactorBlock).map factorBlockValue).prod) = 4469320301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_193
      · exact prime_oneHundredThirtyThreeEA_231571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4469320301) ^ 2234660150 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4469320301) ^ 893864060 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4469320301) ^ 23157100 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4469320301) ^ 19300 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4794607739 : Nat.Prime 4794607739 := by
  apply lucas_primality 4794607739 (2 : ZMod 4794607739)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (104230603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (104230603, 1)] : List FactorBlock).map factorBlockValue).prod) = 4794607739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_104230603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4794607739) ^ 2397303869 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4794607739) ^ 208461206 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4794607739) ^ 46 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4959861037 : Nat.Prime 4959861037 := by
  apply lucas_primality 4959861037 (2 : ZMod 4959861037)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4959861037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_97
      · exact prime_oneHundredThirtyThreeEA_14251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4959861037) ^ 2479930518 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 1653287012 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 381527772 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 215646132 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 51132588 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 348036 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_5324400491 : Nat.Prime 5324400491 := by
  apply lucas_primality 5324400491 (2 : ZMod 5324400491)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) = 5324400491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_6959
      · exact prime_oneHundredThirtyThreeEA_76511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5324400491) ^ 2662200245 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 1064880098 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 765110 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 69590 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_5728663727 : Nat.Prime 5728663727 := by
  apply lucas_primality 5728663727 (5 : ZMod 5728663727)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2864331863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2864331863, 1)] : List FactorBlock).map factorBlockValue).prod) = 5728663727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2864331863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 5728663727) ^ 2864331863 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5728663727) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_6182656693 : Nat.Prime 6182656693 := by
  apply lucas_primality 6182656693 (5 : ZMod 6182656693)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (367, 1), (503, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (367, 1), (503, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) = 6182656693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_367
      · exact prime_oneHundredThirtyThreeEA_503
      · exact prime_oneHundredThirtyThreeEA_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6182656693) ^ 3091328346 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182656693) ^ 2060885564 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182656693) ^ 16846476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182656693) ^ 12291564 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6182656693) ^ 2215212 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_311
      · exact prime_oneHundredThirtyThreeEA_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_7060555979 : Nat.Prime 7060555979 := by
  apply lucas_primality 7060555979 (2 : ZMod 7060555979)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (223, 1), (2261549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (223, 1), (2261549, 1)] : List FactorBlock).map factorBlockValue).prod) = 7060555979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_223
      · exact prime_oneHundredThirtyThreeEA_2261549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7060555979) ^ 3530277989 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7060555979) ^ 1008650854 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7060555979) ^ 31661686 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7060555979) ^ 3122 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_9589215479 : Nat.Prime 9589215479 := by
  apply lucas_primality 9589215479 (7 : ZMod 9589215479)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4794607739, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4794607739, 1)] : List FactorBlock).map factorBlockValue).prod) = 9589215479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_4794607739
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 9589215479) ^ 4794607739 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 9589215479) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_9609435119 : Nat.Prime 9609435119 := by
  apply lucas_primality 9609435119 (7 : ZMod 9609435119)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (281, 1), (551569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (281, 1), (551569, 1)] : List FactorBlock).map factorBlockValue).prod) = 9609435119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_281
      · exact prime_oneHundredThirtyThreeEA_551569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 9609435119) ^ 4804717559 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 9609435119) ^ 309981778 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 9609435119) ^ 34197278 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 9609435119) ^ 17422 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_9957505687 : Nat.Prime 9957505687 := by
  apply lucas_primality 9957505687 (21 : ZMod 9957505687)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1659584281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1659584281, 1)] : List FactorBlock).map factorBlockValue).prod) = 9957505687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_1659584281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (21 : ZMod 9957505687) ^ 4978752843 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (21 : ZMod 9957505687) ^ 3319168562 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (21 : ZMod 9957505687) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11273492801 : Nat.Prime 11273492801 := by
  apply lucas_primality 11273492801 (11 : ZMod 11273492801)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 2), (1583, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 2), (1583, 1), (4451, 1)] : List FactorBlock).map factorBlockValue).prod) = 11273492801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_1583
      · exact prime_oneHundredThirtyThreeEA_4451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11273492801) ^ 5636746400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 11273492801) ^ 2254698560 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 11273492801) ^ 7121600 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 11273492801) ^ 2532800 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11343106013 : Nat.Prime 11343106013 := by
  apply lucas_primality 11343106013 (2 : ZMod 11343106013)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (2687, 1), (150767, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (2687, 1), (150767, 1)] : List FactorBlock).map factorBlockValue).prod) = 11343106013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_2687
      · exact prime_oneHundredThirtyThreeEA_150767
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11343106013) ^ 5671553006 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11343106013) ^ 1620443716 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11343106013) ^ 4221476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11343106013) ^ 75236 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11730422401 : Nat.Prime 11730422401 := by
  apply lucas_primality 11730422401 (7 : ZMod 11730422401)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (5, 2), (311, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (5, 2), (311, 1), (3929, 1)] : List FactorBlock).map factorBlockValue).prod) = 11730422401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_311
      · exact prime_oneHundredThirtyThreeEA_3929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11730422401) ^ 5865211200 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11730422401) ^ 3910140800 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11730422401) ^ 2346084480 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11730422401) ^ 37718400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11730422401) ^ 2985600 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_13878385627 : Nat.Prime 13878385627 := by
  apply lucas_primality 13878385627 (2 : ZMod 13878385627)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (197, 1), (1677349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (197, 1), (1677349, 1)] : List FactorBlock).map factorBlockValue).prod) = 13878385627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_197
      · exact prime_oneHundredThirtyThreeEA_1677349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13878385627) ^ 6939192813 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13878385627) ^ 4626128542 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13878385627) ^ 1982626518 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13878385627) ^ 70448658 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 13878385627) ^ 8274 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_17939860349 : Nat.Prime 17939860349 := by
  apply lucas_primality 17939860349 (2 : ZMod 17939860349)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (199, 1), (2087, 1), (10799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (199, 1), (2087, 1), (10799, 1)] : List FactorBlock).map factorBlockValue).prod) = 17939860349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_199
      · exact prime_oneHundredThirtyThreeEA_2087
      · exact prime_oneHundredThirtyThreeEA_10799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17939860349) ^ 8969930174 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17939860349) ^ 90150052 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17939860349) ^ 8596004 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17939860349) ^ 1661252 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_18126503819 : Nat.Prime 18126503819 := by
  apply lucas_primality 18126503819 (2 : ZMod 18126503819)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (53, 1), (1031, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (53, 1), (1031, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 18126503819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_1031
      · exact prime_oneHundredThirtyThreeEA_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18126503819) ^ 9063251909 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18126503819) ^ 385670294 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18126503819) ^ 342009506 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18126503819) ^ 17581478 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18126503819) ^ 5136442 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_18211719299 : Nat.Prime 18211719299 := by
  apply lucas_primality 18211719299 (6 : ZMod 18211719299)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (131, 1), (491, 1), (7451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (131, 1), (491, 1), (7451, 1)] : List FactorBlock).map factorBlockValue).prod) = 18211719299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_131
      · exact prime_oneHundredThirtyThreeEA_491
      · exact prime_oneHundredThirtyThreeEA_7451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 18211719299) ^ 9105859649 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 18211719299) ^ 958511542 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 18211719299) ^ 139020758 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 18211719299) ^ 37091078 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 18211719299) ^ 2444198 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_19218870239 : Nat.Prime 19218870239 := by
  apply lucas_primality 19218870239 (7 : ZMod 19218870239)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9609435119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9609435119, 1)] : List FactorBlock).map factorBlockValue).prod) = 19218870239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_9609435119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 19218870239) ^ 9609435119 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 19218870239) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22546985603 : Nat.Prime 22546985603 := by
  apply lucas_primality 22546985603 (2 : ZMod 22546985603)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11273492801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11273492801, 1)] : List FactorBlock).map factorBlockValue).prod) = 22546985603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11273492801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 22546985603) ^ 11273492801 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22546985603) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_26093503127 : Nat.Prime 26093503127 := by
  apply lucas_primality 26093503127 (5 : ZMod 26093503127)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25747, 1), (506729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25747, 1), (506729, 1)] : List FactorBlock).map factorBlockValue).prod) = 26093503127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_25747
      · exact prime_oneHundredThirtyThreeEA_506729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 26093503127) ^ 13046751563 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26093503127) ^ 1013458 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26093503127) ^ 51494 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_26815921807 : Nat.Prime 26815921807 := by
  apply lucas_primality 26815921807 (3 : ZMod 26815921807)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4469320301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4469320301, 1)] : List FactorBlock).map factorBlockValue).prod) = 26815921807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_4469320301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 26815921807) ^ 13407960903 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 26815921807) ^ 8938640602 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 26815921807) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_28071727573 : Nat.Prime 28071727573 := by
  apply lucas_primality 28071727573 (2 : ZMod 28071727573)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (334187233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (334187233, 1)] : List FactorBlock).map factorBlockValue).prod) = 28071727573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_334187233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 28071727573) ^ 14035863786 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28071727573) ^ 9357242524 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28071727573) ^ 4010246796 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28071727573) ^ 84 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_29034844343 : Nat.Prime 29034844343 := by
  apply lucas_primality 29034844343 (5 : ZMod 29034844343)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (66900563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (66900563, 1)] : List FactorBlock).map factorBlockValue).prod) = 29034844343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_66900563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 29034844343) ^ 14517422171 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 29034844343) ^ 4147834906 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 29034844343) ^ 936607882 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 29034844343) ^ 434 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_32039942261 : Nat.Prime 32039942261 := by
  apply lucas_primality 32039942261 (2 : ZMod 32039942261)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1601997113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1601997113, 1)] : List FactorBlock).map factorBlockValue).prod) = 32039942261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_1601997113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 32039942261) ^ 16019971130 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32039942261) ^ 6407988452 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 32039942261) ^ 20 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_37588625663 : Nat.Prime 37588625663 := by
  apply lucas_primality 37588625663 (5 : ZMod 37588625663)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2684901833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2684901833, 1)] : List FactorBlock).map factorBlockValue).prod) = 37588625663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_2684901833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 37588625663) ^ 18794312831 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 37588625663) ^ 5369803666 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 37588625663) ^ 14 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_39933114467 : Nat.Prime 39933114467 := by
  apply lucas_primality 39933114467 (5 : ZMod 39933114467)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39933114467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_4801
      · exact prime_oneHundredThirtyThreeEA_594119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39933114467) ^ 19966557233 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 5704730638 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 8317666 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 67214 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_50083708229 : Nat.Prime 50083708229 := by
  apply lucas_primality 50083708229 (2 : ZMod 50083708229)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (401, 1), (463, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (401, 1), (463, 1), (3967, 1)] : List FactorBlock).map factorBlockValue).prod) = 50083708229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_401
      · exact prime_oneHundredThirtyThreeEA_463
      · exact prime_oneHundredThirtyThreeEA_3967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 50083708229) ^ 25041854114 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50083708229) ^ 2946100484 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50083708229) ^ 124897028 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50083708229) ^ 108172156 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 50083708229) ^ 12625084 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_56547777607 : Nat.Prime 56547777607 := by
  apply lucas_primality 56547777607 (23 : ZMod 56547777607)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (211, 1), (271, 1), (164821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (211, 1), (271, 1), (164821, 1)] : List FactorBlock).map factorBlockValue).prod) = 56547777607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_211
      · exact prime_oneHundredThirtyThreeEA_271
      · exact prime_oneHundredThirtyThreeEA_164821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 56547777607) ^ 28273888803 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (23 : ZMod 56547777607) ^ 18849259202 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (23 : ZMod 56547777607) ^ 267998946 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (23 : ZMod 56547777607) ^ 208663386 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (23 : ZMod 56547777607) ^ 343086 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_74163045833 : Nat.Prime 74163045833 := by
  apply lucas_primality 74163045833 (3 : ZMod 74163045833)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (457, 1), (699493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (457, 1), (699493, 1)] : List FactorBlock).map factorBlockValue).prod) = 74163045833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_29
      · exact prime_oneHundredThirtyThreeEA_457
      · exact prime_oneHundredThirtyThreeEA_699493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 74163045833) ^ 37081522916 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 74163045833) ^ 2557346408 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 74163045833) ^ 162282376 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 74163045833) ^ 106024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_76222844497 : Nat.Prime 76222844497 := by
  apply lucas_primality 76222844497 (10 : ZMod 76222844497)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (9227, 1), (57367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (9227, 1), (57367, 1)] : List FactorBlock).map factorBlockValue).prod) = 76222844497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_9227
      · exact prime_oneHundredThirtyThreeEA_57367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 76222844497) ^ 38111422248 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 76222844497) ^ 25407614832 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 76222844497) ^ 8260848 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 76222844497) ^ 1328688 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_88631475817 : Nat.Prime 88631475817 := by
  apply lucas_primality 88631475817 (5 : ZMod 88631475817)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 88631475817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_43
      · exact prime_oneHundredThirtyThreeEA_67
      · exact prime_oneHundredThirtyThreeEA_151
      · exact prime_oneHundredThirtyThreeEA_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88631475817) ^ 44315737908 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 29543825272 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 6817805832 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 2061197112 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 1322857848 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 586963416 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 135729672 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_99539367071 : Nat.Prime 99539367071 := by
  apply lucas_primality 99539367071 (11 : ZMod 99539367071)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (69607949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (69607949, 1)] : List FactorBlock).map factorBlockValue).prod) = 99539367071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_69607949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 99539367071) ^ 49769683535 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99539367071) ^ 19907873414 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99539367071) ^ 9049033370 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99539367071) ^ 7656874390 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 99539367071) ^ 1430 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_106604704321 : Nat.Prime 106604704321 := by
  apply lucas_primality 106604704321 (7 : ZMod 106604704321)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 1), (17, 1), (823, 1), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 1), (17, 1), (823, 1), (7937, 1)] : List FactorBlock).map factorBlockValue).prod) = 106604704321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_823
      · exact prime_oneHundredThirtyThreeEA_7937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 106604704321) ^ 53302352160 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 106604704321) ^ 35534901440 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 106604704321) ^ 21320940864 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 106604704321) ^ 6270864960 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 106604704321) ^ 129531840 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 106604704321) ^ 13431360 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_118356756277 : Nat.Prime 118356756277 := by
  apply lucas_primality 118356756277 (2 : ZMod 118356756277)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) = 118356756277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_896642093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118356756277) ^ 59178378138 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 39452252092 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 10759705116 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 132 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_121544393833 : Nat.Prime 121544393833 := by
  apply lucas_primality 121544393833 (13 : ZMod 121544393833)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (187568509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (187568509, 1)] : List FactorBlock).map factorBlockValue).prod) = 121544393833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_187568509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 121544393833) ^ 60772196916 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 121544393833) ^ 40514797944 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 121544393833) ^ 648 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_132887578169 : Nat.Prime 132887578169 := by
  apply lucas_primality 132887578169 (3 : ZMod 132887578169)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (61, 1), (1279, 1), (212909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (61, 1), (1279, 1), (212909, 1)] : List FactorBlock).map factorBlockValue).prod) = 132887578169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_1279
      · exact prime_oneHundredThirtyThreeEA_212909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 132887578169) ^ 66443789084 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 132887578169) ^ 2178484888 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 132887578169) ^ 103899592 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 132887578169) ^ 624152 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_89
      · exact prime_oneHundredThirtyThreeEA_373
      · exact prime_oneHundredThirtyThreeEA_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_173448217567 : Nat.Prime 173448217567 := by
  apply lucas_primality 173448217567 (3 : ZMod 173448217567)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (13, 2), (2903, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (13, 2), (2903, 1), (6547, 1)] : List FactorBlock).map factorBlockValue).prod) = 173448217567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_2903
      · exact prime_oneHundredThirtyThreeEA_6547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 173448217567) ^ 86724108783 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 173448217567) ^ 57816072522 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 173448217567) ^ 13342170582 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 173448217567) ^ 59747922 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 173448217567) ^ 26492778 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_194207366471 : Nat.Prime 194207366471 := by
  apply lucas_primality 194207366471 (17 : ZMod 194207366471)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (67, 1), (22297057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (67, 1), (22297057, 1)] : List FactorBlock).map factorBlockValue).prod) = 194207366471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_67
      · exact prime_oneHundredThirtyThreeEA_22297057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 194207366471) ^ 97103683235 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 194207366471) ^ 38841473294 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 194207366471) ^ 14939028190 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 194207366471) ^ 2898617410 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 194207366471) ^ 8710 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_298802939503 : Nat.Prime 298802939503 := by
  apply lucas_primality 298802939503 (3 : ZMod 298802939503)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (241, 1), (7125553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (241, 1), (7125553, 1)] : List FactorBlock).map factorBlockValue).prod) = 298802939503 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_29
      · exact prime_oneHundredThirtyThreeEA_241
      · exact prime_oneHundredThirtyThreeEA_7125553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 298802939503) ^ 149401469751 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 298802939503) ^ 99600979834 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 298802939503) ^ 10303549638 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 298802939503) ^ 1239846222 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 298802939503) ^ 41934 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_3931
      · exact prime_oneHundredThirtyThreeEA_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_346744787437 : Nat.Prime 346744787437 := by
  apply lucas_primality 346744787437 (2 : ZMod 346744787437)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (10667, 1), (902953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (10667, 1), (902953, 1)] : List FactorBlock).map factorBlockValue).prod) = 346744787437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_10667
      · exact prime_oneHundredThirtyThreeEA_902953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 346744787437) ^ 173372393718 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 346744787437) ^ 115581595812 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 346744787437) ^ 32506308 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 346744787437) ^ 384012 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_394050764021 : Nat.Prime 394050764021 := by
  apply lucas_primality 394050764021 (3 : ZMod 394050764021)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (839, 1), (809771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (839, 1), (809771, 1)] : List FactorBlock).map factorBlockValue).prod) = 394050764021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_29
      · exact prime_oneHundredThirtyThreeEA_839
      · exact prime_oneHundredThirtyThreeEA_809771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 394050764021) ^ 197025382010 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394050764021) ^ 78810152804 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394050764021) ^ 13587957380 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394050764021) ^ 469667180 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 394050764021) ^ 486620 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_472986682277 : Nat.Prime 472986682277 := by
  apply lucas_primality 472986682277 (2 : ZMod 472986682277)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) = 472986682277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_113
      · exact prime_oneHundredThirtyThreeEA_269
      · exact prime_oneHundredThirtyThreeEA_659
      · exact prime_oneHundredThirtyThreeEA_5903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472986682277) ^ 236493341138 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 4185722852 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 1758314804 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 717733964 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 80126492 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_483879947753 : Nat.Prime 483879947753 := by
  apply lucas_primality 483879947753 (3 : ZMod 483879947753)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4001, 1), (15117469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4001, 1), (15117469, 1)] : List FactorBlock).map factorBlockValue).prod) = 483879947753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_4001
      · exact prime_oneHundredThirtyThreeEA_15117469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 483879947753) ^ 241939973876 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 483879947753) ^ 120939752 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 483879947753) ^ 32008 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_521791248119 : Nat.Prime 521791248119 := by
  apply lucas_primality 521791248119 (7 : ZMod 521791248119)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) = 521791248119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_5324400491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 521791248119) ^ 260895624059 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 74541606874 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 98 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_729266362999 : Nat.Prime 729266362999 := by
  apply lucas_primality 729266362999 (3 : ZMod 729266362999)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (121544393833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (121544393833, 1)] : List FactorBlock).map factorBlockValue).prod) = 729266362999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_121544393833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 729266362999) ^ 364633181499 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 729266362999) ^ 243088787666 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 729266362999) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_907448481041 : Nat.Prime 907448481041 := by
  apply lucas_primality 907448481041 (3 : ZMod 907448481041)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11343106013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11343106013, 1)] : List FactorBlock).map factorBlockValue).prod) = 907448481041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_11343106013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 907448481041) ^ 453724240520 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 907448481041) ^ 181489696208 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 907448481041) ^ 80 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1012662998143 : Nat.Prime 1012662998143 := by
  apply lucas_primality 1012662998143 (5 : ZMod 1012662998143)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5657, 1), (29835101, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5657, 1), (29835101, 1)] : List FactorBlock).map factorBlockValue).prod) = 1012662998143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5657
      · exact prime_oneHundredThirtyThreeEA_29835101
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1012662998143) ^ 506331499071 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1012662998143) ^ 337554332714 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1012662998143) ^ 179010606 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1012662998143) ^ 33942 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1721088942029 : Nat.Prime 1721088942029 := by
  apply lucas_primality 1721088942029 (2 : ZMod 1721088942029)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2467, 1), (174411121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2467, 1), (174411121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1721088942029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2467
      · exact prime_oneHundredThirtyThreeEA_174411121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1721088942029) ^ 860544471014 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1721088942029) ^ 697644484 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1721088942029) ^ 9868 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1731099241327 : Nat.Prime 1731099241327 := by
  apply lucas_primality 1731099241327 (3 : ZMod 1731099241327)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (3170511431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (3170511431, 1)] : List FactorBlock).map factorBlockValue).prod) = 1731099241327 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_3170511431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1731099241327) ^ 865549620663 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1731099241327) ^ 577033080442 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1731099241327) ^ 247299891618 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1731099241327) ^ 133161480102 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1731099241327) ^ 546 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1885825531357 : Nat.Prime 1885825531357 := by
  apply lucas_primality 1885825531357 (5 : ZMod 1885825531357)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (179, 1), (67534219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (179, 1), (67534219, 1)] : List FactorBlock).map factorBlockValue).prod) = 1885825531357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_179
      · exact prime_oneHundredThirtyThreeEA_67534219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1885825531357) ^ 942912765678 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885825531357) ^ 628608510452 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885825531357) ^ 145063502412 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885825531357) ^ 10535338164 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1885825531357) ^ 27924 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2048623959419 : Nat.Prime 2048623959419 := by
  apply lucas_primality 2048623959419 (2 : ZMod 2048623959419)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (479, 1), (2138438371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (479, 1), (2138438371, 1)] : List FactorBlock).map factorBlockValue).prod) = 2048623959419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_479
      · exact prime_oneHundredThirtyThreeEA_2138438371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2048623959419) ^ 1024311979709 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048623959419) ^ 4276876742 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2048623959419) ^ 958 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2114468589007 : Nat.Prime 2114468589007 := by
  apply lucas_primality 2114468589007 (3 : ZMod 2114468589007)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (6182656693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (6182656693, 1)] : List FactorBlock).map factorBlockValue).prod) = 2114468589007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_6182656693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2114468589007) ^ 1057234294503 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114468589007) ^ 704822863002 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114468589007) ^ 111287820474 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2114468589007) ^ 342 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2397625820273 : Nat.Prime 2397625820273 := by
  apply lucas_primality 2397625820273 (3 : ZMod 2397625820273)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (53, 1), (41149, 1), (68711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (53, 1), (41149, 1), (68711, 1)] : List FactorBlock).map factorBlockValue).prod) = 2397625820273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_41149
      · exact prime_oneHundredThirtyThreeEA_68711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2397625820273) ^ 1198812910136 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397625820273) ^ 45238223024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397625820273) ^ 58266928 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2397625820273) ^ 34894352 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2612270659513 : Nat.Prime 2612270659513 := by
  apply lucas_primality 2612270659513 (10 : ZMod 2612270659513)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (5728663727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (5728663727, 1)] : List FactorBlock).map factorBlockValue).prod) = 2612270659513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_5728663727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2612270659513) ^ 1306135329756 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2612270659513) ^ 870756886504 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2612270659513) ^ 137487929448 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 2612270659513) ^ 456 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4103412749251 : Nat.Prime 4103412749251 := by
  apply lucas_primality 4103412749251 (2 : ZMod 4103412749251)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (25411, 1), (215309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (25411, 1), (215309, 1)] : List FactorBlock).map factorBlockValue).prod) = 4103412749251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_25411
      · exact prime_oneHundredThirtyThreeEA_215309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4103412749251) ^ 2051706374625 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103412749251) ^ 1367804249750 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103412749251) ^ 820682549850 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103412749251) ^ 161481750 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4103412749251) ^ 19058250 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4453002562033 : Nat.Prime 4453002562033 := by
  apply lucas_primality 4453002562033 (5 : ZMod 4453002562033)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 5), (137, 1), (1789, 1), (4673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 5), (137, 1), (1789, 1), (4673, 1)] : List FactorBlock).map factorBlockValue).prod) = 4453002562033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_137
      · exact prime_oneHundredThirtyThreeEA_1789
      · exact prime_oneHundredThirtyThreeEA_4673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4453002562033) ^ 2226501281016 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4453002562033) ^ 1484334187344 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4453002562033) ^ 32503668336 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4453002562033) ^ 2489101488 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4453002562033) ^ 952921584 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4919939684483 : Nat.Prime 4919939684483 := by
  apply lucas_primality 4919939684483 (2 : ZMod 4919939684483)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (12323, 1), (2734579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (12323, 1), (2734579, 1)] : List FactorBlock).map factorBlockValue).prod) = 4919939684483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_73
      · exact prime_oneHundredThirtyThreeEA_12323
      · exact prime_oneHundredThirtyThreeEA_2734579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4919939684483) ^ 2459969842241 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4919939684483) ^ 67396434034 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4919939684483) ^ 399248534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4919939684483) ^ 1799158 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_9424600020163 : Nat.Prime 9424600020163 := by
  apply lucas_primality 9424600020163 (3 : ZMod 9424600020163)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (35951, 1), (4854653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (35951, 1), (4854653, 1)] : List FactorBlock).map factorBlockValue).prod) = 9424600020163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_35951
      · exact prime_oneHundredThirtyThreeEA_4854653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9424600020163) ^ 4712300010081 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9424600020163) ^ 3141533340054 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9424600020163) ^ 262151262 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 9424600020163) ^ 1941354 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_10403988322733 : Nat.Prime 10403988322733 := by
  apply lucas_primality 10403988322733 (2 : ZMod 10403988322733)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) = 10403988322733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1303
      · exact prime_oneHundredThirtyThreeEA_2383
      · exact prime_oneHundredThirtyThreeEA_837667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10403988322733) ^ 5201994161366 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 7984641844 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 4365920404 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 12420196 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11129029575289 : Nat.Prime 11129029575289 := by
  apply lucas_primality 11129029575289 (7 : ZMod 11129029575289)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (3181, 1), (3101591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (3181, 1), (3101591, 1)] : List FactorBlock).map factorBlockValue).prod) = 11129029575289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_3181
      · exact prime_oneHundredThirtyThreeEA_3101591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11129029575289) ^ 5564514787644 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11129029575289) ^ 3709676525096 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11129029575289) ^ 236787863304 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11129029575289) ^ 3498594648 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11129029575289) ^ 3588168 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11575400810473 : Nat.Prime 11575400810473 := by
  apply lucas_primality 11575400810473 (5 : ZMod 11575400810473)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (71, 1), (754786177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (71, 1), (754786177, 1)] : List FactorBlock).map factorBlockValue).prod) = 11575400810473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_71
      · exact prime_oneHundredThirtyThreeEA_754786177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11575400810473) ^ 5787700405236 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11575400810473) ^ 3858466936824 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11575400810473) ^ 163033814232 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 11575400810473) ^ 15336 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11612252629051 : Nat.Prime 11612252629051 := by
  apply lucas_primality 11612252629051 (2 : ZMod 11612252629051)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (29, 1), (37, 1), (72148199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (29, 1), (37, 1), (72148199, 1)] : List FactorBlock).map factorBlockValue).prod) = 11612252629051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_29
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_72148199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11612252629051) ^ 5806126314525 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11612252629051) ^ 3870750876350 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11612252629051) ^ 2322450525810 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11612252629051) ^ 400422504450 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11612252629051) ^ 313844665650 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11612252629051) ^ 160950 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_12269199679907 : Nat.Prime 12269199679907 := by
  apply lucas_primality 12269199679907 (2 : ZMod 12269199679907)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 2), (19, 1), (1910495123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 2), (19, 1), (1910495123, 1)] : List FactorBlock).map factorBlockValue).prod) = 12269199679907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_1910495123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 12269199679907) ^ 6134599839953 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12269199679907) ^ 943784590762 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12269199679907) ^ 645747351574 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 12269199679907) ^ 6422 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22118381824309 : Nat.Prime 22118381824309 := by
  apply lucas_primality 22118381824309 (10 : ZMod 22118381824309)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (11, 1), (347, 1), (68984561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (11, 1), (347, 1), (68984561, 1)] : List FactorBlock).map factorBlockValue).prod) = 22118381824309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_347
      · exact prime_oneHundredThirtyThreeEA_68984561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 22118381824309) ^ 11059190912154 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 22118381824309) ^ 7372793941436 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 22118381824309) ^ 3159768832044 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 22118381824309) ^ 2010761984028 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 22118381824309) ^ 63741734364 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 22118381824309) ^ 320628 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_24151281055201 : Nat.Prime 24151281055201 := by
  apply lucas_primality 24151281055201 (14 : ZMod 24151281055201)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 2), (13, 1), (258026507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 2), (13, 1), (258026507, 1)] : List FactorBlock).map factorBlockValue).prod) = 24151281055201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_258026507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 24151281055201) ^ 12075640527600 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (14 : ZMod 24151281055201) ^ 8050427018400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (14 : ZMod 24151281055201) ^ 4830256211040 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (14 : ZMod 24151281055201) ^ 1857790850400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (14 : ZMod 24151281055201) ^ 93600 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_26042758597571 : Nat.Prime 26042758597571 := by
  apply lucas_primality 26042758597571 (7 : ZMod 26042758597571)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (13, 1), (18211719299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (13, 1), (18211719299, 1)] : List FactorBlock).map factorBlockValue).prod) = 26042758597571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_18211719299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 26042758597571) ^ 13021379298785 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 26042758597571) ^ 5208551719514 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 26042758597571) ^ 2367523508870 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 26042758597571) ^ 2003289122890 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 26042758597571) ^ 1430 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_27112534959361 : Nat.Prime 27112534959361 := by
  apply lucas_primality 27112534959361 (7 : ZMod 27112534959361)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (7060555979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (7060555979, 1)] : List FactorBlock).map factorBlockValue).prod) = 27112534959361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7060555979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 27112534959361) ^ 13556267479680 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27112534959361) ^ 9037511653120 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27112534959361) ^ 5422506991872 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 27112534959361) ^ 3840 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_30271993327859 : Nat.Prime 30271993327859 := by
  apply lucas_primality 30271993327859 (2 : ZMod 30271993327859)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (107, 1), (229, 1), (982067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (107, 1), (229, 1), (982067, 1)] : List FactorBlock).map factorBlockValue).prod) = 30271993327859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_107
      · exact prime_oneHundredThirtyThreeEA_229
      · exact prime_oneHundredThirtyThreeEA_982067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 30271993327859) ^ 15135996663929 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30271993327859) ^ 1780705489874 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30271993327859) ^ 818161981834 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30271993327859) ^ 282915825494 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30271993327859) ^ 132192110602 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30271993327859) ^ 30824774 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_34263212775643 : Nat.Prime 34263212775643 := by
  apply lucas_primality 34263212775643 (2 : ZMod 34263212775643)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (420757, 1), (4524017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (420757, 1), (4524017, 1)] : List FactorBlock).map factorBlockValue).prod) = 34263212775643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_420757
      · exact prime_oneHundredThirtyThreeEA_4524017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34263212775643) ^ 17131606387821 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34263212775643) ^ 11421070925214 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34263212775643) ^ 81432306 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34263212775643) ^ 7573626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_35481804872093 : Nat.Prime 35481804872093 := by
  apply lucas_primality 35481804872093 (3 : ZMod 35481804872093)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) = 35481804872093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_521791248119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35481804872093) ^ 17740902436046 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 2087164992476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 68 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_47314481425193 : Nat.Prime 47314481425193 := by
  apply lucas_primality 47314481425193 (3 : ZMod 47314481425193)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (239, 1), (523, 1), (1631573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (239, 1), (523, 1), (1631573, 1)] : List FactorBlock).map factorBlockValue).prod) = 47314481425193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_29
      · exact prime_oneHundredThirtyThreeEA_239
      · exact prime_oneHundredThirtyThreeEA_523
      · exact prime_oneHundredThirtyThreeEA_1631573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47314481425193) ^ 23657240712596 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47314481425193) ^ 1631533842248 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47314481425193) ^ 197968541528 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47314481425193) ^ 90467459704 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47314481425193) ^ 28999304 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_52085517195143 : Nat.Prime 52085517195143 := by
  apply lucas_primality 52085517195143 (5 : ZMod 52085517195143)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (26042758597571, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (26042758597571, 1)] : List FactorBlock).map factorBlockValue).prod) = 52085517195143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_26042758597571
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 52085517195143) ^ 26042758597571 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 52085517195143) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_55139171718977 : Nat.Prime 55139171718977 := by
  apply lucas_primality 55139171718977 (3 : ZMod 55139171718977)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (251, 1), (3432468359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (251, 1), (3432468359, 1)] : List FactorBlock).map factorBlockValue).prod) = 55139171718977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_251
      · exact prime_oneHundredThirtyThreeEA_3432468359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55139171718977) ^ 27569585859488 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 55139171718977) ^ 219677974976 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 55139171718977) ^ 16064 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_65236970750209 : Nat.Prime 65236970750209 := by
  apply lucas_primality 65236970750209 (7 : ZMod 65236970750209)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (43, 1), (1975441217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (43, 1), (1975441217, 1)] : List FactorBlock).map factorBlockValue).prod) = 65236970750209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_43
      · exact prime_oneHundredThirtyThreeEA_1975441217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 65236970750209) ^ 32618485375104 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 65236970750209) ^ 21745656916736 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 65236970750209) ^ 1517138854656 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 65236970750209) ^ 33024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_67261843675717 : Nat.Prime 67261843675717 := by
  apply lucas_primality 67261843675717 (2 : ZMod 67261843675717)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (19, 1), (617, 1), (28125473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (19, 1), (617, 1), (28125473, 1)] : List FactorBlock).map factorBlockValue).prod) = 67261843675717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_617
      · exact prime_oneHundredThirtyThreeEA_28125473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67261843675717) ^ 33630921837858 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67261843675717) ^ 22420614558572 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67261843675717) ^ 3956579039748 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67261843675717) ^ 3540097035564 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67261843675717) ^ 109014333348 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 67261843675717) ^ 2391492 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_70753820440643 : Nat.Prime 70753820440643 := by
  apply lucas_primality 70753820440643 (2 : ZMod 70753820440643)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) = 70753820440643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_431
      · exact prime_oneHundredThirtyThreeEA_54833
      · exact prime_oneHundredThirtyThreeEA_1496927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70753820440643) ^ 35376910220321 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 164161996382 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 1290351074 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 47266046 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_87423725448053 : Nat.Prime 87423725448053 := by
  apply lucas_primality 87423725448053 (2 : ZMod 87423725448053)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (323053, 1), (9664903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (323053, 1), (9664903, 1)] : List FactorBlock).map factorBlockValue).prod) = 87423725448053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_323053
      · exact prime_oneHundredThirtyThreeEA_9664903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87423725448053) ^ 43711862724026 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87423725448053) ^ 12489103635436 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87423725448053) ^ 270617284 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 87423725448053) ^ 9045484 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_139067338396643 : Nat.Prime 139067338396643 := by
  apply lucas_primality 139067338396643 (2 : ZMod 139067338396643)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2477, 1), (28071727573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2477, 1), (28071727573, 1)] : List FactorBlock).map factorBlockValue).prod) = 139067338396643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2477
      · exact prime_oneHundredThirtyThreeEA_28071727573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 139067338396643) ^ 69533669198321 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139067338396643) ^ 56143455146 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139067338396643) ^ 4954 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_191190308885861 : Nat.Prime 191190308885861 := by
  apply lucas_primality 191190308885861 (2 : ZMod 191190308885861)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (83, 1), (257, 1), (448151303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (83, 1), (257, 1), (448151303, 1)] : List FactorBlock).map factorBlockValue).prod) = 191190308885861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_83
      · exact prime_oneHundredThirtyThreeEA_257
      · exact prime_oneHundredThirtyThreeEA_448151303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 191190308885861) ^ 95595154442930 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 191190308885861) ^ 38238061777172 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 191190308885861) ^ 2303497697420 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 191190308885861) ^ 743931162980 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 191190308885861) ^ 426620 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_195700202914807 : Nat.Prime 195700202914807 := by
  apply lucas_primality 195700202914807 (3 : ZMod 195700202914807)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (431, 1), (103889, 1), (242813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (431, 1), (103889, 1), (242813, 1)] : List FactorBlock).map factorBlockValue).prod) = 195700202914807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_431
      · exact prime_oneHundredThirtyThreeEA_103889
      · exact prime_oneHundredThirtyThreeEA_242813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 195700202914807) ^ 97850101457403 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 195700202914807) ^ 65233400971602 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 195700202914807) ^ 454060795626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 195700202914807) ^ 1883743254 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 195700202914807) ^ 805970862 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_251236300778753 : Nat.Prime 251236300778753 := by
  apply lucas_primality 251236300778753 (3 : ZMod 251236300778753)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (1129, 1), (869257573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (1129, 1), (869257573, 1)] : List FactorBlock).map factorBlockValue).prod) = 251236300778753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1129
      · exact prime_oneHundredThirtyThreeEA_869257573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 251236300778753) ^ 125618150389376 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 251236300778753) ^ 222529938688 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 251236300778753) ^ 289024 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_298219943744717 : Nat.Prime 298219943744717 := by
  apply lucas_primality 298219943744717 (2 : ZMod 298219943744717)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (107, 1), (99539367071, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (107, 1), (99539367071, 1)] : List FactorBlock).map factorBlockValue).prod) = 298219943744717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_107
      · exact prime_oneHundredThirtyThreeEA_99539367071
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 298219943744717) ^ 149109971872358 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 298219943744717) ^ 42602849106388 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 298219943744717) ^ 2787102277988 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 298219943744717) ^ 2996 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_701
      · exact prime_oneHundredThirtyThreeEA_9769
      · exact prime_oneHundredThirtyThreeEA_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_625249011082109 : Nat.Prime 625249011082109 := by
  apply lucas_primality 625249011082109 (2 : ZMod 625249011082109)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) = 625249011082109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_71
      · exact prime_oneHundredThirtyThreeEA_181
      · exact prime_oneHundredThirtyThreeEA_91454369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625249011082109) ^ 312624505541054 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 89321287297444 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 32907842688532 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 8806324099748 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 3454414425868 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 6836732 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1115331887063311 : Nat.Prime 1115331887063311 := by
  apply lucas_primality 1115331887063311 (7 : ZMod 1115331887063311)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115331887063311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_39933114467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1115331887063311) ^ 557665943531655 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 371777295687770 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 223066377412662 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 159333126723330 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 58701678266490 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 27930 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2005209950649127 : Nat.Prime 2005209950649127 := by
  apply lucas_primality 2005209950649127 (3 : ZMod 2005209950649127)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1433, 1), (17939860349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1433, 1), (17939860349, 1)] : List FactorBlock).map factorBlockValue).prod) = 2005209950649127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_1433
      · exact prime_oneHundredThirtyThreeEA_17939860349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2005209950649127) ^ 1002604975324563 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2005209950649127) ^ 668403316883042 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2005209950649127) ^ 154246919280702 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2005209950649127) ^ 1399309107222 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2005209950649127) ^ 111774 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2092076674290523 : Nat.Prime 2092076674290523 := by
  apply lucas_primality 2092076674290523 (5 : ZMod 2092076674290523)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4003, 1), (29034844343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4003, 1), (29034844343, 1)] : List FactorBlock).map factorBlockValue).prod) = 2092076674290523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_4003
      · exact prime_oneHundredThirtyThreeEA_29034844343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2092076674290523) ^ 1046038337145261 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2092076674290523) ^ 697358891430174 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2092076674290523) ^ 522627198174 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2092076674290523) ^ 72054 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2139920090441051 : Nat.Prime 2139920090441051 := by
  apply lucas_primality 2139920090441051 (2 : ZMod 2139920090441051)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2139920090441051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_83
      · exact prime_oneHundredThirtyThreeEA_347
      · exact prime_oneHundredThirtyThreeEA_653
      · exact prime_oneHundredThirtyThreeEA_2275657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2139920090441051) ^ 1069960045220525 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 427984018088210 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 25782169764350 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 6166916687150 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 3277059862850 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 940352650 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4184193320283577 : Nat.Prime 4184193320283577 := by
  apply lucas_primality 4184193320283577 (5 : ZMod 4184193320283577)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (59, 2), (50083708229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (59, 2), (50083708229, 1)] : List FactorBlock).map factorBlockValue).prod) = 4184193320283577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_59
      · exact prime_oneHundredThirtyThreeEA_50083708229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4184193320283577) ^ 2092096660141788 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4184193320283577) ^ 1394731106761192 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4184193320283577) ^ 70918530852264 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4184193320283577) ^ 83544 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_7180872508276979 : Nat.Prime 7180872508276979 := by
  apply lucas_primality 7180872508276979 (2 : ZMod 7180872508276979)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (166259, 1), (3085062853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (166259, 1), (3085062853, 1)] : List FactorBlock).map factorBlockValue).prod) = 7180872508276979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_166259
      · exact prime_oneHundredThirtyThreeEA_3085062853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7180872508276979) ^ 3590436254138489 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7180872508276979) ^ 1025838929753854 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7180872508276979) ^ 43190879942 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 7180872508276979) ^ 2327626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_7670080870169143 : Nat.Prime 7670080870169143 := by
  apply lucas_primality 7670080870169143 (3 : ZMod 7670080870169143)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (48991, 1), (26093503127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (48991, 1), (26093503127, 1)] : List FactorBlock).map factorBlockValue).prod) = 7670080870169143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_48991
      · exact prime_oneHundredThirtyThreeEA_26093503127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7670080870169143) ^ 3835040435084571 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7670080870169143) ^ 2556693623389714 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7670080870169143) ^ 156561018762 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7670080870169143) ^ 293946 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_7752654287094377 : Nat.Prime 7752654287094377 := by
  apply lucas_primality 7752654287094377 (3 : ZMod 7752654287094377)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (307, 1), (4999, 1), (57404539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (307, 1), (4999, 1), (57404539, 1)] : List FactorBlock).map factorBlockValue).prod) = 7752654287094377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_307
      · exact prime_oneHundredThirtyThreeEA_4999
      · exact prime_oneHundredThirtyThreeEA_57404539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7752654287094377) ^ 3876327143547188 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7752654287094377) ^ 704786753372216 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7752654287094377) ^ 25252945560568 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7752654287094377) ^ 1550841025624 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7752654287094377) ^ 135052984 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_8289176853448999 : Nat.Prime 8289176853448999 := by
  apply lucas_primality 8289176853448999 (6 : ZMod 8289176853448999)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (1321, 1), (26815921807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (1321, 1), (26815921807, 1)] : List FactorBlock).map factorBlockValue).prod) = 8289176853448999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_1321
      · exact prime_oneHundredThirtyThreeEA_26815921807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 8289176853448999) ^ 4144588426724499 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8289176853448999) ^ 2763058951149666 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8289176853448999) ^ 637628988726846 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8289176853448999) ^ 6274925702838 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 8289176853448999) ^ 309114 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_11027102167252991 : Nat.Prime 11027102167252991 := by
  apply lucas_primality 11027102167252991 (7 : ZMod 11027102167252991)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (13, 1), (1731099241327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (13, 1), (1731099241327, 1)] : List FactorBlock).map factorBlockValue).prod) = 11027102167252991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_1731099241327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11027102167252991) ^ 5513551083626495 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11027102167252991) ^ 2205420433450598 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11027102167252991) ^ 1575300309607570 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11027102167252991) ^ 848238628250230 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 11027102167252991) ^ 6370 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_12792448223820593 : Nat.Prime 12792448223820593 := by
  apply lucas_primality 12792448223820593 (3 : ZMod 12792448223820593)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (61, 1), (88663, 1), (147829609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (61, 1), (88663, 1), (147829609, 1)] : List FactorBlock).map factorBlockValue).prod) = 12792448223820593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_88663
      · exact prime_oneHundredThirtyThreeEA_147829609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 12792448223820593) ^ 6396224111910296 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12792448223820593) ^ 209712265964272 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12792448223820593) ^ 144281698384 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 12792448223820593) ^ 86535088 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_20007968354627489 : Nat.Prime 20007968354627489 := by
  apply lucas_primality 20007968354627489 (3 : ZMod 20007968354627489)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) = 20007968354627489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_625249011082109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20007968354627489) ^ 10003984177313744 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20007968354627489) ^ 32 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_21622823765946191 : Nat.Prime 21622823765946191 := by
  apply lucas_primality 21622823765946191 (17 : ZMod 21622823765946191)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (67, 1), (127, 1), (719, 1), (9552197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (67, 1), (127, 1), (719, 1), (9552197, 1)] : List FactorBlock).map factorBlockValue).prod) = 21622823765946191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_67
      · exact prime_oneHundredThirtyThreeEA_127
      · exact prime_oneHundredThirtyThreeEA_719
      · exact prime_oneHundredThirtyThreeEA_9552197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 21622823765946191) ^ 10811411882973095 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 4324564753189238 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 584400642322870 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 322728712924570 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 170258454849970 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 30073468381010 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 21622823765946191) ^ 2263649270 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22054204334505983 : Nat.Prime 22054204334505983 := by
  apply lucas_primality 22054204334505983 (5 : ZMod 22054204334505983)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11027102167252991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11027102167252991, 1)] : List FactorBlock).map factorBlockValue).prod) = 22054204334505983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11027102167252991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 22054204334505983) ^ 11027102167252991 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 22054204334505983) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_25105159921701463 : Nat.Prime 25105159921701463 := by
  apply lucas_primality 25105159921701463 (5 : ZMod 25105159921701463)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4184193320283577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4184193320283577, 1)] : List FactorBlock).map factorBlockValue).prod) = 25105159921701463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_4184193320283577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 25105159921701463) ^ 12552579960850731 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25105159921701463) ^ 8368386640567154 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25105159921701463) ^ 6 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_28189529219092531 : Nat.Prime 28189529219092531 := by
  apply lucas_primality 28189529219092531 (2 : ZMod 28189529219092531)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (48479, 1), (1140155257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (48479, 1), (1140155257, 1)] : List FactorBlock).map factorBlockValue).prod) = 28189529219092531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_48479
      · exact prime_oneHundredThirtyThreeEA_1140155257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28189529219092531) ^ 14094764609546265 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28189529219092531) ^ 9396509739697510 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28189529219092531) ^ 5637905843818506 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28189529219092531) ^ 1658207601123090 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28189529219092531) ^ 581479181070 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28189529219092531) ^ 24724290 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_145829
      · exact prime_oneHundredThirtyThreeEA_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_54192618628544989 : Nat.Prime 54192618628544989 := by
  apply lucas_primality 54192618628544989 (6 : ZMod 54192618628544989)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (17, 1), (61, 1), (483879947753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (17, 1), (61, 1), (483879947753, 1)] : List FactorBlock).map factorBlockValue).prod) = 54192618628544989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_61
      · exact prime_oneHundredThirtyThreeEA_483879947753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 54192618628544989) ^ 27096309314272494 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 54192618628544989) ^ 18064206209514996 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 54192618628544989) ^ 3187801095796764 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 54192618628544989) ^ 888403584074508 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 54192618628544989) ^ 111996 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_61981970667002831 : Nat.Prime 61981970667002831 := by
  apply lucas_primality 61981970667002831 (11 : ZMod 61981970667002831)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (131, 1), (47314481425193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (131, 1), (47314481425193, 1)] : List FactorBlock).map factorBlockValue).prod) = 61981970667002831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_131
      · exact prime_oneHundredThirtyThreeEA_47314481425193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 61981970667002831) ^ 30990985333501415 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 61981970667002831) ^ 12396394133400566 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 61981970667002831) ^ 473144814251930 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 61981970667002831) ^ 1310 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_75704580130795409 : Nat.Prime 75704580130795409 := by
  apply lucas_primality 75704580130795409 (3 : ZMod 75704580130795409)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (193, 1), (1885825531357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (193, 1), (1885825531357, 1)] : List FactorBlock).map factorBlockValue).prod) = 75704580130795409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_193
      · exact prime_oneHundredThirtyThreeEA_1885825531357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 75704580130795409) ^ 37852290065397704 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 75704580130795409) ^ 5823429240830416 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 75704580130795409) ^ 392251710522256 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 75704580130795409) ^ 40144 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_108840765245108443 : Nat.Prime 108840765245108443 := by
  apply lucas_primality 108840765245108443 (2 : ZMod 108840765245108443)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 2), (19, 1), (613, 1), (11777, 1), (111791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 2), (19, 1), (613, 1), (11777, 1), (111791, 1)] : List FactorBlock).map factorBlockValue).prod) = 108840765245108443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_613
      · exact prime_oneHundredThirtyThreeEA_11777
      · exact prime_oneHundredThirtyThreeEA_111791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 108840765245108443) ^ 54420382622554221 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 36280255081702814 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 15548680749301206 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 8372366557316034 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 5728461328689918 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 177554266305234 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 9241807357146 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 108840765245108443) ^ 973609371462 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_115841347831601807 : Nat.Prime 115841347831601807 := by
  apply lucas_primality 115841347831601807 (5 : ZMod 115841347831601807)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1151, 1), (2273, 1), (2333, 1), (9489517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1151, 1), (2273, 1), (2333, 1), (9489517, 1)] : List FactorBlock).map factorBlockValue).prod) = 115841347831601807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1151
      · exact prime_oneHundredThirtyThreeEA_2273
      · exact prime_oneHundredThirtyThreeEA_2333
      · exact prime_oneHundredThirtyThreeEA_9489517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 115841347831601807) ^ 57920673915800903 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115841347831601807) ^ 100644090209906 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115841347831601807) ^ 50964077356622 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115841347831601807) ^ 49653385268582 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 115841347831601807) ^ 12207296518 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_139479003957209123 : Nat.Prime 139479003957209123 := by
  apply lucas_primality 139479003957209123 (2 : ZMod 139479003957209123)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (17293, 1), (21517, 1), (1348379, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (17293, 1), (21517, 1), (1348379, 1)] : List FactorBlock).map factorBlockValue).prod) = 139479003957209123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_139
      · exact prime_oneHundredThirtyThreeEA_17293
      · exact prime_oneHundredThirtyThreeEA_21517
      · exact prime_oneHundredThirtyThreeEA_1348379
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 139479003957209123) ^ 69739501978604561 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139479003957209123) ^ 1003446071634598 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139479003957209123) ^ 8065633722154 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139479003957209123) ^ 6482270017066 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 139479003957209123) ^ 103441987718 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_306700989194377763 : Nat.Prime 306700989194377763 := by
  apply lucas_primality 306700989194377763 (2 : ZMod 306700989194377763)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1992257, 1), (974344927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1992257, 1), (974344927, 1)] : List FactorBlock).map factorBlockValue).prod) = 306700989194377763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_79
      · exact prime_oneHundredThirtyThreeEA_1992257
      · exact prime_oneHundredThirtyThreeEA_974344927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 306700989194377763) ^ 153350494597188881 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 306700989194377763) ^ 3882291002460478 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 306700989194377763) ^ 153946498466 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 306700989194377763) ^ 314776606 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_378693463456599601 : Nat.Prime 378693463456599601 := by
  apply lucas_primality 378693463456599601 (11 : ZMod 378693463456599601)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (19, 1), (23, 1), (422701, 1), (1708409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (19, 1), (23, 1), (422701, 1), (1708409, 1)] : List FactorBlock).map factorBlockValue).prod) = 378693463456599601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_422701
      · exact prime_oneHundredThirtyThreeEA_1708409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 378693463456599601) ^ 189346731728299800 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 126231154485533200 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 75738692691319920 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 19931234918768400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 16464933193765200 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 895889679600 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 378693463456599601) ^ 221664404400 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_434279548061398199 : Nat.Prime 434279548061398199 := by
  apply lucas_primality 434279548061398199 (19 : ZMod 434279548061398199)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (101, 1), (823, 1), (2612270659513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (101, 1), (823, 1), (2612270659513, 1)] : List FactorBlock).map factorBlockValue).prod) = 434279548061398199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_101
      · exact prime_oneHundredThirtyThreeEA_823
      · exact prime_oneHundredThirtyThreeEA_2612270659513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 434279548061398199) ^ 217139774030699099 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 434279548061398199) ^ 4299797505558398 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 434279548061398199) ^ 527678673221626 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (19 : ZMod 434279548061398199) ^ 166246 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_435871723482055901 : Nat.Prime 435871723482055901 := by
  apply lucas_primality 435871723482055901 (2 : ZMod 435871723482055901)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 1), (53, 1), (349, 1), (18126503819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 1), (53, 1), (349, 1), (18126503819, 1)] : List FactorBlock).map factorBlockValue).prod) = 435871723482055901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_349
      · exact prime_oneHundredThirtyThreeEA_18126503819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435871723482055901) ^ 217935861741027950 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 435871723482055901) ^ 87174344696411180 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 435871723482055901) ^ 33528594114004300 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 435871723482055901) ^ 8223994782680300 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 435871723482055901) ^ 1248916113129100 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 435871723482055901) ^ 24046100 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_841983229614766891 : Nat.Prime 841983229614766891 := by
  apply lucas_primality 841983229614766891 (3 : ZMod 841983229614766891)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) = 841983229614766891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_113
      · exact prime_oneHundredThirtyThreeEA_35481804872093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841983229614766891) ^ 420991614807383445 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 280661076538255630 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 168396645922953378 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 120283318516395270 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 7451179023139530 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 23730 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1089151483564018307 : Nat.Prime 1089151483564018307 := by
  apply lucas_primality 1089151483564018307 (2 : ZMod 1089151483564018307)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (7670080870169143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (7670080870169143, 1)] : List FactorBlock).map factorBlockValue).prod) = 1089151483564018307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_71
      · exact prime_oneHundredThirtyThreeEA_7670080870169143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1089151483564018307) ^ 544575741782009153 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1089151483564018307) ^ 15340161740338286 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1089151483564018307) ^ 142 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1298224515520902401 : Nat.Prime 1298224515520902401 := by
  apply lucas_primality 1298224515520902401 (3 : ZMod 1298224515520902401)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 2), (1630933, 1), (124375177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 2), (1630933, 1), (124375177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1298224515520902401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_1630933
      · exact prime_oneHundredThirtyThreeEA_124375177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1298224515520902401) ^ 649112257760451200 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 259644903104180480 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 796001132800 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1298224515520902401) ^ 10437971200 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1474995841761370283 : Nat.Prime 1474995841761370283 := by
  apply lucas_primality 1474995841761370283 (2 : ZMod 1474995841761370283)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2473, 1), (298219943744717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2473, 1), (298219943744717, 1)] : List FactorBlock).map factorBlockValue).prod) = 1474995841761370283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_2473
      · exact prime_oneHundredThirtyThreeEA_298219943744717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1474995841761370283) ^ 737497920880685141 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474995841761370283) ^ 596439887489434 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1474995841761370283) ^ 4946 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2191282786973904497 : Nat.Prime 2191282786973904497 := by
  apply lucas_primality 2191282786973904497 (3 : ZMod 2191282786973904497)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (179, 1), (305411, 1), (2505190399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (179, 1), (305411, 1), (2505190399, 1)] : List FactorBlock).map factorBlockValue).prod) = 2191282786973904497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_179
      · exact prime_oneHundredThirtyThreeEA_305411
      · exact prime_oneHundredThirtyThreeEA_2505190399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2191282786973904497) ^ 1095641393486952248 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2191282786973904497) ^ 12241803279183824 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2191282786973904497) ^ 7174865302736 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2191282786973904497) ^ 874697104 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3560394780600186131 : Nat.Prime 3560394780600186131 := by
  apply lucas_primality 3560394780600186131 (2 : ZMod 3560394780600186131)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (23, 1), (109793, 1), (2877395683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (23, 1), (109793, 1), (2877395683, 1)] : List FactorBlock).map factorBlockValue).prod) = 3560394780600186131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_109793
      · exact prime_oneHundredThirtyThreeEA_2877395683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3560394780600186131) ^ 1780197390300093065 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560394780600186131) ^ 712078956120037226 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560394780600186131) ^ 508627825800026590 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560394780600186131) ^ 154799773069573310 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560394780600186131) ^ 32428249347410 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3560394780600186131) ^ 1237367110 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4090810064022186847 : Nat.Prime 4090810064022186847 := by
  apply lucas_primality 4090810064022186847 (3 : ZMod 4090810064022186847)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (61981970667002831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (61981970667002831, 1)] : List FactorBlock).map factorBlockValue).prod) = 4090810064022186847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_61981970667002831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4090810064022186847) ^ 2045405032011093423 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4090810064022186847) ^ 1363603354674062282 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4090810064022186847) ^ 371891824002016986 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4090810064022186847) ^ 66 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4397133934882509917 : Nat.Prime 4397133934882509917 := by
  apply lucas_primality 4397133934882509917 (2 : ZMod 4397133934882509917)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (89597, 1), (12269199679907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (89597, 1), (12269199679907, 1)] : List FactorBlock).map factorBlockValue).prod) = 4397133934882509917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_89597
      · exact prime_oneHundredThirtyThreeEA_12269199679907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4397133934882509917) ^ 2198566967441254958 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4397133934882509917) ^ 49076798719628 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4397133934882509917) ^ 358388 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_5857720873778091187 : Nat.Prime 5857720873778091187 := by
  apply lucas_primality 5857720873778091187 (2 : ZMod 5857720873778091187)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 1), (67, 1), (1931, 1), (76222844497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 1), (67, 1), (1931, 1), (76222844497, 1)] : List FactorBlock).map factorBlockValue).prod) = 5857720873778091187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_67
      · exact prime_oneHundredThirtyThreeEA_1931
      · exact prime_oneHundredThirtyThreeEA_76222844497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5857720873778091187) ^ 2928860436889045593 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5857720873778091187) ^ 1952573624592697062 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5857720873778091187) ^ 532520079434371926 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5857720873778091187) ^ 87428669757881958 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5857720873778091187) ^ 3033516765291606 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5857720873778091187) ^ 76849938 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_5860769857415332747 : Nat.Prime 5860769857415332747 := by
  apply lucas_primality 5860769857415332747 (5 : ZMod 5860769857415332747)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2817043, 1), (346744787437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2817043, 1), (346744787437, 1)] : List FactorBlock).map factorBlockValue).prod) = 5860769857415332747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_2817043
      · exact prime_oneHundredThirtyThreeEA_346744787437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 5860769857415332747) ^ 2930384928707666373 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5860769857415332747) ^ 1953589952471777582 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5860769857415332747) ^ 2080468724622 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5860769857415332747) ^ 16902258 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_18628311609451359889 : Nat.Prime 18628311609451359889 := by
  apply lucas_primality 18628311609451359889 (7 : ZMod 18628311609451359889)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (163, 1), (76717, 1), (150979, 1), (205559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (163, 1), (76717, 1), (150979, 1), (205559, 1)] : List FactorBlock).map factorBlockValue).prod) = 18628311609451359889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_163
      · exact prime_oneHundredThirtyThreeEA_76717
      · exact prime_oneHundredThirtyThreeEA_150979
      · exact prime_oneHundredThirtyThreeEA_205559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 18628311609451359889) ^ 9314155804725679944 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18628311609451359889) ^ 6209437203150453296 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18628311609451359889) ^ 114284120303382576 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18628311609451359889) ^ 242818561850064 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18628311609451359889) ^ 123383461338672 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 18628311609451359889) ^ 90622700098032 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_24694625805007836103 : Nat.Prime 24694625805007836103 := by
  apply lucas_primality 24694625805007836103 (5 : ZMod 24694625805007836103)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (21031, 1), (195700202914807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (21031, 1), (195700202914807, 1)] : List FactorBlock).map factorBlockValue).prod) = 24694625805007836103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_21031
      · exact prime_oneHundredThirtyThreeEA_195700202914807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 24694625805007836103) ^ 12347312902503918051 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 24694625805007836103) ^ 8231541935002612034 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 24694625805007836103) ^ 1174201217488842 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 24694625805007836103) ^ 126186 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_25070581079864877929 : Nat.Prime 25070581079864877929 := by
  apply lucas_primality 25070581079864877929 (3 : ZMod 25070581079864877929)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (44959949, 1), (9957505687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (44959949, 1), (9957505687, 1)] : List FactorBlock).map factorBlockValue).prod) = 25070581079864877929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_44959949
      · exact prime_oneHundredThirtyThreeEA_9957505687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25070581079864877929) ^ 12535290539932438964 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25070581079864877929) ^ 3581511582837839704 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25070581079864877929) ^ 557620318472 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25070581079864877929) ^ 2517757144 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_35676823002993275099 : Nat.Prime 35676823002993275099 := by
  apply lucas_primality 35676823002993275099 (2 : ZMod 35676823002993275099)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (102845747, 1), (173448217567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (102845747, 1), (173448217567, 1)] : List FactorBlock).map factorBlockValue).prod) = 35676823002993275099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_102845747
      · exact prime_oneHundredThirtyThreeEA_173448217567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 35676823002993275099) ^ 17838411501496637549 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35676823002993275099) ^ 346896435134 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35676823002993275099) ^ 205691494 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_37227626794343685263 : Nat.Prime 37227626794343685263 := by
  apply lucas_primality 37227626794343685263 (5 : ZMod 37227626794343685263)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1123, 1), (6496283, 1), (2551471159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1123, 1), (6496283, 1), (2551471159, 1)] : List FactorBlock).map factorBlockValue).prod) = 37227626794343685263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1123
      · exact prime_oneHundredThirtyThreeEA_6496283
      · exact prime_oneHundredThirtyThreeEA_2551471159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 37227626794343685263) ^ 18613813397171842631 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 37227626794343685263) ^ 33150157430403994 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 37227626794343685263) ^ 5730604223114 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 37227626794343685263) ^ 14590651618 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_198754457937897546827 : Nat.Prime 198754457937897546827 := by
  apply lucas_primality 198754457937897546827 (2 : ZMod 198754457937897546827)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1091, 1), (37991, 1), (2397625820273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1091, 1), (37991, 1), (2397625820273, 1)] : List FactorBlock).map factorBlockValue).prod) = 198754457937897546827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1091
      · exact prime_oneHundredThirtyThreeEA_37991
      · exact prime_oneHundredThirtyThreeEA_2397625820273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 198754457937897546827) ^ 99377228968948773413 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198754457937897546827) ^ 182176405075983086 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198754457937897546827) ^ 5231619539835686 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198754457937897546827) ^ 82896362 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_73
      · exact prime_oneHundredThirtyThreeEA_79
      · exact prime_oneHundredThirtyThreeEA_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_270591572109975110887 : Nat.Prime 270591572109975110887 := by
  apply lucas_primality 270591572109975110887 (3 : ZMod 270591572109975110887)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (670493, 1), (67261843675717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (670493, 1), (67261843675717, 1)] : List FactorBlock).map factorBlockValue).prod) = 270591572109975110887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_670493
      · exact prime_oneHundredThirtyThreeEA_67261843675717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 270591572109975110887) ^ 135295786054987555443 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 270591572109975110887) ^ 90197190703325036962 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 270591572109975110887) ^ 403571062054302 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 270591572109975110887) ^ 4022958 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_304655345905837250297 : Nat.Prime 304655345905837250297 := by
  apply lucas_primality 304655345905837250297 (3 : ZMod 304655345905837250297)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (293, 1), (479, 1), (110951, 1), (349370653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (293, 1), (479, 1), (110951, 1), (349370653, 1)] : List FactorBlock).map factorBlockValue).prod) = 304655345905837250297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_293
      · exact prime_oneHundredThirtyThreeEA_479
      · exact prime_oneHundredThirtyThreeEA_110951
      · exact prime_oneHundredThirtyThreeEA_349370653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 304655345905837250297) ^ 152327672952918625148 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 304655345905837250297) ^ 43522192272262464328 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 304655345905837250297) ^ 1039779337562584472 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 304655345905837250297) ^ 636023686651017224 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 304655345905837250297) ^ 2745854890049096 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 304655345905837250297) ^ 872011839832 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_478365987136687493741 : Nat.Prime 478365987136687493741 := by
  apply lucas_primality 478365987136687493741 (2 : ZMod 478365987136687493741)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (1063, 1), (16421, 1), (42953, 1), (2453921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (1063, 1), (16421, 1), (42953, 1), (2453921, 1)] : List FactorBlock).map factorBlockValue).prod) = 478365987136687493741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_1063
      · exact prime_oneHundredThirtyThreeEA_16421
      · exact prime_oneHundredThirtyThreeEA_42953
      · exact prime_oneHundredThirtyThreeEA_2453921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 478365987136687493741) ^ 239182993568343746870 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 95673197427337498748 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 36797383625899037980 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 450015039639404980 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 29131355406898940 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 11136963358477580 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 478365987136687493741) ^ 194939440648940 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_490733665773440592071 : Nat.Prime 490733665773440592071 := by
  apply lucas_primality 490733665773440592071 (7 : ZMod 490733665773440592071)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (257, 1), (3463, 1), (55139171718977, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (257, 1), (3463, 1), (55139171718977, 1)] : List FactorBlock).map factorBlockValue).prod) = 490733665773440592071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_257
      · exact prime_oneHundredThirtyThreeEA_3463
      · exact prime_oneHundredThirtyThreeEA_55139171718977
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 490733665773440592071) ^ 245366832886720296035 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 490733665773440592071) ^ 98146733154688118414 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 490733665773440592071) ^ 1909469516628173510 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 490733665773440592071) ^ 141707671317770890 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 490733665773440592071) ^ 8899910 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_638774596226615859541 : Nat.Prime 638774596226615859541 := by
  apply lucas_primality 638774596226615859541 (10 : ZMod 638774596226615859541)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (47, 1), (131, 1), (4729, 1), (12289, 1), (9917909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (47, 1), (131, 1), (4729, 1), (12289, 1), (9917909, 1)] : List FactorBlock).map factorBlockValue).prod) = 638774596226615859541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_131
      · exact prime_oneHundredThirtyThreeEA_4729
      · exact prime_oneHundredThirtyThreeEA_12289
      · exact prime_oneHundredThirtyThreeEA_9917909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 638774596226615859541) ^ 319387298113307929770 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 212924865408871953180 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 127754919245323171908 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 13590948855885443820 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 4876141955928365340 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 135076040648470260 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 51979379626219860 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 638774596226615859541) ^ 64406176365060 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_696922749607807983613 : Nat.Prime 696922749607807983613 := by
  apply lucas_primality 696922749607807983613 (5 : ZMod 696922749607807983613)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (2633, 1), (2005209950649127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (2633, 1), (2005209950649127, 1)] : List FactorBlock).map factorBlockValue).prod) = 696922749607807983613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_2633
      · exact prime_oneHundredThirtyThreeEA_2005209950649127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 696922749607807983613) ^ 348461374803903991806 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 696922749607807983613) ^ 232307583202602661204 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 696922749607807983613) ^ 63356613600709816692 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 696922749607807983613) ^ 264687713485684764 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 696922749607807983613) ^ 347556 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_802258594555676093729 : Nat.Prime 802258594555676093729 := by
  apply lucas_primality 802258594555676093729 (3 : ZMod 802258594555676093729)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (25070581079864877929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (25070581079864877929, 1)] : List FactorBlock).map factorBlockValue).prod) = 802258594555676093729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_25070581079864877929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 802258594555676093729) ^ 401129297277838046864 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 802258594555676093729) ^ 32 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1604517189111352187459 : Nat.Prime 1604517189111352187459 := by
  apply lucas_primality 1604517189111352187459 (2 : ZMod 1604517189111352187459)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (802258594555676093729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (802258594555676093729, 1)] : List FactorBlock).map factorBlockValue).prod) = 1604517189111352187459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_802258594555676093729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 1604517189111352187459) ^ 802258594555676093729 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1604517189111352187459) ^ 2 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3030732763954101504971 : Nat.Prime 3030732763954101504971 := by
  apply lucas_primality 3030732763954101504971 (6 : ZMod 3030732763954101504971)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (20476153, 1), (2114468589007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (20476153, 1), (2114468589007, 1)] : List FactorBlock).map factorBlockValue).prod) = 3030732763954101504971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_20476153
      · exact prime_oneHundredThirtyThreeEA_2114468589007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3030732763954101504971) ^ 1515366381977050752485 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3030732763954101504971) ^ 606146552790820300994 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3030732763954101504971) ^ 432961823422014500710 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3030732763954101504971) ^ 148012801230490 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3030732763954101504971) ^ 1433330710 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3577580242882155842887 : Nat.Prime 3577580242882155842887 := by
  apply lucas_primality 3577580242882155842887 (6 : ZMod 3577580242882155842887)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (198754457937897546827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (198754457937897546827, 1)] : List FactorBlock).map factorBlockValue).prod) = 3577580242882155842887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_198754457937897546827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 3577580242882155842887) ^ 1788790121441077921443 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3577580242882155842887) ^ 1192526747627385280962 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 3577580242882155842887) ^ 18 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4102538900190732922901 : Nat.Prime 4102538900190732922901 := by
  apply lucas_primality 4102538900190732922901 (2 : ZMod 4102538900190732922901)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (5860769857415332747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (5860769857415332747, 1)] : List FactorBlock).map factorBlockValue).prod) = 4102538900190732922901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_5860769857415332747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4102538900190732922901) ^ 2051269450095366461450 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4102538900190732922901) ^ 820507780038146584580 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4102538900190732922901) ^ 586076985741533274700 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4102538900190732922901) ^ 700 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4935320595542126592563 : Nat.Prime 4935320595542126592563 := by
  apply lucas_primality 4935320595542126592563 (2 : ZMod 4935320595542126592563)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (63211, 1), (526387, 1), (74163045833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (63211, 1), (526387, 1), (74163045833, 1)] : List FactorBlock).map factorBlockValue).prod) = 4935320595542126592563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_63211
      · exact prime_oneHundredThirtyThreeEA_526387
      · exact prime_oneHundredThirtyThreeEA_74163045833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4935320595542126592563) ^ 2467660297771063296281 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4935320595542126592563) ^ 78076926413790742 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4935320595542126592563) ^ 9375840580299526 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4935320595542126592563) ^ 66546897314 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_6747600002509315318177 : Nat.Prime 6747600002509315318177 := by
  apply lucas_primality 6747600002509315318177 (5 : ZMod 6747600002509315318177)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (3733, 1), (2092076674290523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (3733, 1), (2092076674290523, 1)] : List FactorBlock).map factorBlockValue).prod) = 6747600002509315318177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_3733
      · exact prime_oneHundredThirtyThreeEA_2092076674290523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6747600002509315318177) ^ 3373800001254657659088 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6747600002509315318177) ^ 2249200000836438439392 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6747600002509315318177) ^ 1807554246587011872 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6747600002509315318177) ^ 3225312 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_7488998344362023941087 : Nat.Prime 7488998344362023941087 := by
  apply lucas_primality 7488998344362023941087 (3 : ZMod 7488998344362023941087)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7488998344362023941087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_3515265851
      · exact prime_oneHundredThirtyThreeEA_118356756277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7488998344362023941087) ^ 3744499172181011970543 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2496332781454007980362 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2130421612986 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 63274785318 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_19443931067650780582693 : Nat.Prime 19443931067650780582693 := by
  apply lucas_primality 19443931067650780582693 (2 : ZMod 19443931067650780582693)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11617, 1), (139479003957209123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11617, 1), (139479003957209123, 1)] : List FactorBlock).map factorBlockValue).prod) = 19443931067650780582693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11617
      · exact prime_oneHundredThirtyThreeEA_139479003957209123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19443931067650780582693) ^ 9721965533825390291346 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19443931067650780582693) ^ 6481310355883593527564 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19443931067650780582693) ^ 1673748047486509476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19443931067650780582693) ^ 139404 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_20432221788810149231377 : Nat.Prime 20432221788810149231377 := by
  apply lucas_primality 20432221788810149231377 (5 : ZMod 20432221788810149231377)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (31, 1), (8123, 1), (1768157, 1), (956038507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (31, 1), (8123, 1), (1768157, 1), (956038507, 1)] : List FactorBlock).map factorBlockValue).prod) = 20432221788810149231377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_8123
      · exact prime_oneHundredThirtyThreeEA_1768157
      · exact prime_oneHundredThirtyThreeEA_956038507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 20432221788810149231377) ^ 10216110894405074615688 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20432221788810149231377) ^ 6810740596270049743792 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20432221788810149231377) ^ 659103928671295136496 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20432221788810149231377) ^ 2515354153491339312 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20432221788810149231377) ^ 11555660379033168 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 20432221788810149231377) ^ 21371756094768 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_30659886273587040541681 : Nat.Prime 30659886273587040541681 := by
  apply lucas_primality 30659886273587040541681 (17 : ZMod 30659886273587040541681)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (149, 1), (1571, 1), (4103412749251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (19, 1), (149, 1), (1571, 1), (4103412749251, 1)] : List FactorBlock).map factorBlockValue).prod) = 30659886273587040541681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_149
      · exact prime_oneHundredThirtyThreeEA_1571
      · exact prime_oneHundredThirtyThreeEA_4103412749251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 30659886273587040541681) ^ 15329943136793520270840 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 10219962091195680180560 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 6131977254717408108336 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 4379983753369577220240 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 1613678224925633712720 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 205771048816020406320 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 19516159308457696080 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 30659886273587040541681) ^ 7471801680 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_46879866739395374386619 : Nat.Prime 46879866739395374386619 := by
  apply lucas_primality 46879866739395374386619 (2 : ZMod 46879866739395374386619)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (478365987136687493741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (478365987136687493741, 1)] : List FactorBlock).map factorBlockValue).prod) = 46879866739395374386619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_478365987136687493741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 46879866739395374386619) ^ 23439933369697687193309 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46879866739395374386619) ^ 6697123819913624912374 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 46879866739395374386619) ^ 98 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_52141756178154185745119 : Nat.Prime 52141756178154185745119 := by
  apply lucas_primality 52141756178154185745119 (7 : ZMod 52141756178154185745119)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (41, 1), (883, 1), (344293, 1), (298802939503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (41, 1), (883, 1), (344293, 1), (298802939503, 1)] : List FactorBlock).map factorBlockValue).prod) = 52141756178154185745119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_41
      · exact prime_oneHundredThirtyThreeEA_883
      · exact prime_oneHundredThirtyThreeEA_344293
      · exact prime_oneHundredThirtyThreeEA_298802939503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 52141756178154185745119) ^ 26070878089077092872559 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 52141756178154185745119) ^ 7448822311164883677874 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 52141756178154185745119) ^ 1271750150686687457198 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 52141756178154185745119) ^ 59050686498475861546 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 52141756178154185745119) ^ 151445879463579526 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 52141756178154185745119) ^ 174502152706 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_74249459371272750773233 : Nat.Prime 74249459371272750773233 := by
  apply lucas_primality 74249459371272750773233 (5 : ZMod 74249459371272750773233)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (173, 1), (27763, 1), (1284341, 1), (6116111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (173, 1), (27763, 1), (1284341, 1), (6116111, 1)] : List FactorBlock).map factorBlockValue).prod) = 74249459371272750773233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_41
      · exact prime_oneHundredThirtyThreeEA_173
      · exact prime_oneHundredThirtyThreeEA_27763
      · exact prime_oneHundredThirtyThreeEA_1284341
      · exact prime_oneHundredThirtyThreeEA_6116111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 74249459371272750773233) ^ 37124729685636375386616 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 24749819790424250257744 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 1810962423689579287152 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 429187626423541911984 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 2674403319932022864 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 57811328433237552 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 74249459371272750773233) ^ 12139979044080912 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_107314132166071464402889 : Nat.Prime 107314132166071464402889 := by
  apply lucas_primality 107314132166071464402889 (22 : ZMod 107314132166071464402889)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (638774596226615859541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (638774596226615859541, 1)] : List FactorBlock).map factorBlockValue).prod) = 107314132166071464402889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_638774596226615859541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (22 : ZMod 107314132166071464402889) ^ 53657066083035732201444 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (22 : ZMod 107314132166071464402889) ^ 35771377388690488134296 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (22 : ZMod 107314132166071464402889) ^ 15330590309438780628984 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (22 : ZMod 107314132166071464402889) ^ 168 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_212649431442274400707307 : Nat.Prime 212649431442274400707307 := by
  apply lucas_primality 212649431442274400707307 (2 : ZMod 212649431442274400707307)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (349, 1), (304655345905837250297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (349, 1), (304655345905837250297, 1)] : List FactorBlock).map factorBlockValue).prod) = 212649431442274400707307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_349
      · exact prime_oneHundredThirtyThreeEA_304655345905837250297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 212649431442274400707307) ^ 106324715721137200353653 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 212649431442274400707307) ^ 609310691811674500594 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 212649431442274400707307) ^ 698 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_312975077249164292158403 : Nat.Prime 312975077249164292158403 := by
  apply lucas_primality 312975077249164292158403 (2 : ZMod 312975077249164292158403)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1301, 1), (1066973, 1), (2761553, 1), (40822129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1301, 1), (1066973, 1), (2761553, 1), (40822129, 1)] : List FactorBlock).map factorBlockValue).prod) = 312975077249164292158403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1301
      · exact prime_oneHundredThirtyThreeEA_1066973
      · exact prime_oneHundredThirtyThreeEA_2761553
      · exact prime_oneHundredThirtyThreeEA_40822129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 312975077249164292158403) ^ 156487538624582146079201 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 312975077249164292158403) ^ 240565009415191615802 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 312975077249164292158403) ^ 293329894242088874 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 312975077249164292158403) ^ 113332996777235234 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 312975077249164292158403) ^ 7666799476557538 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_407184167475490933632541 : Nat.Prime 407184167475490933632541 := by
  apply lucas_primality 407184167475490933632541 (2 : ZMod 407184167475490933632541)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (163, 1), (2191282786973904497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (163, 1), (2191282786973904497, 1)] : List FactorBlock).map factorBlockValue).prod) = 407184167475490933632541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_163
      · exact prime_oneHundredThirtyThreeEA_2191282786973904497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 407184167475490933632541) ^ 203592083737745466816270 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 407184167475490933632541) ^ 135728055825163644544180 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 407184167475490933632541) ^ 81436833495098186726508 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 407184167475490933632541) ^ 21430745656604785980660 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 407184167475490933632541) ^ 2498062377150251126580 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 407184167475490933632541) ^ 185820 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_492841256055224346135919 : Nat.Prime 492841256055224346135919 := by
  apply lucas_primality 492841256055224346135919 (3 : ZMod 492841256055224346135919)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (79, 1), (85303, 1), (11575400810473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (79, 1), (85303, 1), (11575400810473, 1)] : List FactorBlock).map factorBlockValue).prod) = 492841256055224346135919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_79
      · exact prime_oneHundredThirtyThreeEA_85303
      · exact prime_oneHundredThirtyThreeEA_11575400810473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 492841256055224346135919) ^ 246420628027612173067959 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 492841256055224346135919) ^ 164280418685074782045306 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 492841256055224346135919) ^ 37910865850401872779686 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 492841256055224346135919) ^ 6238496912091447419442 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 492841256055224346135919) ^ 5777537203324904706 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (3 : ZMod 492841256055224346135919) ^ 42576603966 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1954840379249293022601677 : Nat.Prime 1954840379249293022601677 := by
  apply lucas_primality 1954840379249293022601677 (2 : ZMod 1954840379249293022601677)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1954840379249293022601677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_373
      · exact prime_oneHundredThirtyThreeEA_125933891
      · exact prime_oneHundredThirtyThreeEA_10403988322733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1954840379249293022601677) ^ 977420189624646511300838 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 5240858925601321776412 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 15522750577517636 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 187893365372 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4602279915286407037962041 : Nat.Prime 4602279915286407037962041 := by
  apply lucas_primality 4602279915286407037962041 (6 : ZMod 4602279915286407037962041)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (47, 1), (324161, 1), (10819147, 1), (99715657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (47, 1), (324161, 1), (10819147, 1), (99715657, 1)] : List FactorBlock).map factorBlockValue).prod) = 4602279915286407037962041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_47
      · exact prime_oneHundredThirtyThreeEA_324161
      · exact prime_oneHundredThirtyThreeEA_10819147
      · exact prime_oneHundredThirtyThreeEA_99715657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4602279915286407037962041) ^ 2301139957643203518981020 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 920455983057281407592408 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 657468559326629576851720 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 97920849261412915701320 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 14197512702905059640 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 425382880488305320 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 4602279915286407037962041) ^ 46154034920377720 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_97
      · exact prime_oneHundredThirtyThreeEA_719
      · exact prime_oneHundredThirtyThreeEA_17207
      · exact prime_oneHundredThirtyThreeEA_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_14756146357514581724757047 : Nat.Prime 14756146357514581724757047 := by
  apply lucas_primality 14756146357514581724757047 (5 : ZMod 14756146357514581724757047)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (897059, 1), (115841347831601807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (897059, 1), (115841347831601807, 1)] : List FactorBlock).map factorBlockValue).prod) = 14756146357514581724757047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_71
      · exact prime_oneHundredThirtyThreeEA_897059
      · exact prime_oneHundredThirtyThreeEA_115841347831601807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 14756146357514581724757047) ^ 7378073178757290862378523 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14756146357514581724757047) ^ 207833047288937770771226 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14756146357514581724757047) ^ 16449471392087456594 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14756146357514581724757047) ^ 127382378 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_17854149606639648331896343 : Nat.Prime 17854149606639648331896343 := by
  apply lucas_primality 17854149606639648331896343 (5 : ZMod 17854149606639648331896343)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 2), (6747600002509315318177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 2), (6747600002509315318177, 1)] : List FactorBlock).map factorBlockValue).prod) = 17854149606639648331896343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_6747600002509315318177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 17854149606639648331896343) ^ 8927074803319824165948171 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17854149606639648331896343) ^ 5951383202213216110632114 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17854149606639648331896343) ^ 2550592800948521190270906 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 17854149606639648331896343) ^ 2646 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_20033315783625351364379041 : Nat.Prime 20033315783625351364379041 := by
  apply lucas_primality 20033315783625351364379041 (17 : ZMod 20033315783625351364379041)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (7, 1), (13, 1), (41210977, 1), (11129029575289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (7, 1), (13, 1), (41210977, 1), (11129029575289, 1)] : List FactorBlock).map factorBlockValue).prod) = 20033315783625351364379041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_41210977
      · exact prime_oneHundredThirtyThreeEA_11129029575289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 20033315783625351364379041) ^ 10016657891812675682189520 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 6677771927875117121459680 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 4006663156725070272875808 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 2861902254803621623482720 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 1541024291048103951106080 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 486116011848623520 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (17 : ZMod 20033315783625351364379041) ^ 1800095475360 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_21140292496057459378732333 : Nat.Prime 21140292496057459378732333 := by
  apply lucas_primality 21140292496057459378732333 (2 : ZMod 21140292496057459378732333)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (11897, 1), (44507, 1), (65236970750209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (11897, 1), (44507, 1), (65236970750209, 1)] : List FactorBlock).map factorBlockValue).prod) = 21140292496057459378732333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_17
      · exact prime_oneHundredThirtyThreeEA_11897
      · exact prime_oneHundredThirtyThreeEA_44507
      · exact prime_oneHundredThirtyThreeEA_65236970750209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21140292496057459378732333) ^ 10570146248028729689366166 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21140292496057459378732333) ^ 7046764165352486459577444 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21140292496057459378732333) ^ 1243546617415144669337196 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21140292496057459378732333) ^ 1776943136593885801356 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21140292496057459378732333) ^ 474988035501324721476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21140292496057459378732333) ^ 324053864748 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22520981894253134182041119 : Nat.Prime 22520981894253134182041119 := by
  apply lucas_primality 22520981894253134182041119 (11 : ZMod 22520981894253134182041119)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (37, 1), (257, 1), (24175577, 1), (4453002562033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (37, 1), (257, 1), (24175577, 1), (4453002562033, 1)] : List FactorBlock).map factorBlockValue).prod) = 22520981894253134182041119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_257
      · exact prime_oneHundredThirtyThreeEA_24175577
      · exact prime_oneHundredThirtyThreeEA_4453002562033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 22520981894253134182041119) ^ 11260490947126567091020559 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 22520981894253134182041119) ^ 2047361990386648562003738 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 22520981894253134182041119) ^ 608675186331165788703814 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 22520981894253134182041119) ^ 87630279744175619385374 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 22520981894253134182041119) ^ 931559229972179534 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (11 : ZMod 22520981894253134182041119) ^ 5057482357246 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22657276020990689172768169 : Nat.Prime 22657276020990689172768169 := by
  apply lucas_primality 22657276020990689172768169 (13 : ZMod 22657276020990689172768169)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (11287, 1), (47659, 1), (205993, 1), (258170491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (11287, 1), (47659, 1), (205993, 1), (258170491, 1)] : List FactorBlock).map factorBlockValue).prod) = 22657276020990689172768169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_11
      · exact prime_oneHundredThirtyThreeEA_11287
      · exact prime_oneHundredThirtyThreeEA_47659
      · exact prime_oneHundredThirtyThreeEA_205993
      · exact prime_oneHundredThirtyThreeEA_258170491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 22657276020990689172768169) ^ 11328638010495344586384084 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 7552425340330229724256056 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 2059752365544608106615288 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 2007378047398838413464 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 475403932541402236152 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 109990514342675183976 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (13 : ZMod 22657276020990689172768169) ^ 87760905335190648 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_33173311304994806510339893 : Nat.Prime 33173311304994806510339893 := by
  apply lucas_primality 33173311304994806510339893 (5 : ZMod 33173311304994806510339893)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (212649431442274400707307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (212649431442274400707307, 1)] : List FactorBlock).map factorBlockValue).prod) = 33173311304994806510339893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_13
      · exact prime_oneHundredThirtyThreeEA_212649431442274400707307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33173311304994806510339893) ^ 16586655652497403255169946 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33173311304994806510339893) ^ 11057770434998268836779964 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33173311304994806510339893) ^ 2551793177307292808487684 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (5 : ZMod 33173311304994806510339893) ^ 156 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_84176389499826222087265039 : Nat.Prime 84176389499826222087265039 := by
  apply lucas_primality 84176389499826222087265039 (7 : ZMod 84176389499826222087265039)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (43, 1), (53, 1), (131, 1), (1667, 1), (28189529219092531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (43, 1), (53, 1), (131, 1), (1667, 1), (28189529219092531, 1)] : List FactorBlock).map factorBlockValue).prod) = 84176389499826222087265039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_43
      · exact prime_oneHundredThirtyThreeEA_53
      · exact prime_oneHundredThirtyThreeEA_131
      · exact prime_oneHundredThirtyThreeEA_1667
      · exact prime_oneHundredThirtyThreeEA_28189529219092531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 84176389499826222087265039) ^ 42088194749913111043632519 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 28058796499942074029088346 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 1957590453484330746215466 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 1588233764147664567684246 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 642567858777299405246298 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 50495734552985136225114 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (7 : ZMod 84176389499826222087265039) ^ 2986087098 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_269710970129803401130379233 : Nat.Prime 269710970129803401130379233 := by
  apply lucas_primality 269710970129803401130379233 (10 : ZMod 269710970129803401130379233)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (103, 1), (3030732763954101504971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (103, 1), (3030732763954101504971, 1)] : List FactorBlock).map factorBlockValue).prod) = 269710970129803401130379233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_103
      · exact prime_oneHundredThirtyThreeEA_3030732763954101504971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 269710970129803401130379233) ^ 134855485064901700565189616 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 269710970129803401130379233) ^ 89903656709934467043459744 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 269710970129803401130379233) ^ 2618553108056343700294944 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 269710970129803401130379233) ^ 88992 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1497538053196908408181058027 : Nat.Prime 1497538053196908408181058027 := by
  apply lucas_primality 1497538053196908408181058027 (2 : ZMod 1497538053196908408181058027)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497538053196908408181058027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_1703297
      · exact prime_oneHundredThirtyThreeEA_4959861037
      · exact prime_oneHundredThirtyThreeEA_88631475817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1497538053196908408181058027) ^ 748769026598454204090529013 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 879199607113092084458 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 301931453729337298 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 16896232849477978 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_1990398678299688390620393581 : Nat.Prime 1990398678299688390620393581 := by
  apply lucas_primality 1990398678299688390620393581 (2 : ZMod 1990398678299688390620393581)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (33173311304994806510339893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (33173311304994806510339893, 1)] : List FactorBlock).map factorBlockValue).prod) = 1990398678299688390620393581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_33173311304994806510339893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1990398678299688390620393581) ^ 995199339149844195310196790 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1990398678299688390620393581) ^ 663466226099896130206797860 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1990398678299688390620393581) ^ 398079735659937678124078716 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1990398678299688390620393581) ^ 60 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_2246307079795362612271587041 : Nat.Prime 2246307079795362612271587041 := by
  apply lucas_primality 2246307079795362612271587041 (6 : ZMod 2246307079795362612271587041)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246307079795362612271587041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_171401
      · exact prime_oneHundredThirtyThreeEA_714027719
      · exact prime_oneHundredThirtyThreeEA_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2246307079795362612271587041) ^ 1123153539897681306135793520 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 449261415959072522454317408 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 118226688410282242751136160 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 13105565777302131331040 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 3145966213946608160 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 372050597795529760 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_3656778967108729833930490531 : Nat.Prime 3656778967108729833930490531 := by
  apply lucas_primality 3656778967108729833930490531 (2 : ZMod 3656778967108729833930490531)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (107, 1), (241, 1), (2579, 1), (157837, 1), (11612252629051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (107, 1), (241, 1), (2579, 1), (157837, 1), (11612252629051, 1)] : List FactorBlock).map factorBlockValue).prod) = 3656778967108729833930490531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_107
      · exact prime_oneHundredThirtyThreeEA_241
      · exact prime_oneHundredThirtyThreeEA_2579
      · exact prime_oneHundredThirtyThreeEA_157837
      · exact prime_oneHundredThirtyThreeEA_11612252629051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3656778967108729833930490531) ^ 1828389483554364916965245265 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 1218926322369576611310163510 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 731355793421745966786098106 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 34175504365502147980658790 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 15173356709994729601371330 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 1417905764679616065890070 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 23168071916652811659690 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3656778967108729833930490531) ^ 314906942169030 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_15724149558567538285901109281 : Nat.Prime 15724149558567538285901109281 := by
  apply lucas_primality 15724149558567538285901109281 (6 : ZMod 15724149558567538285901109281)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 15724149558567538285901109281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_7
      · exact prime_oneHundredThirtyThreeEA_19
      · exact prime_oneHundredThirtyThreeEA_171401
      · exact prime_oneHundredThirtyThreeEA_714027719
      · exact prime_oneHundredThirtyThreeEA_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15724149558567538285901109281) ^ 7862074779283769142950554640 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 3144829911713507657180221856 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 2246307079795362612271587040 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 827586818871975699257953120 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 91738960441114919317280 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 22021763497626257120 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15724149558567538285901109281) ^ 2604354184568708320 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_17471277287297264762112343649 : Nat.Prime 17471277287297264762112343649 := by
  apply lucas_primality 17471277287297264762112343649 (6 : ZMod 17471277287297264762112343649)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (37, 1), (14756146357514581724757047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (37, 1), (14756146357514581724757047, 1)] : List FactorBlock).map factorBlockValue).prod) = 17471277287297264762112343649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_14756146357514581724757047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 17471277287297264762112343649) ^ 8735638643648632381056171824 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 17471277287297264762112343649) ^ 472196683440466615192225504 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (6 : ZMod 17471277287297264762112343649) ^ 1184 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_22463070797953626122715870413 : Nat.Prime 22463070797953626122715870413 := by
  apply lucas_primality 22463070797953626122715870413 (2 : ZMod 22463070797953626122715870413)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) = 22463070797953626122715870413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_23
      · exact prime_oneHundredThirtyThreeEA_32603
      · exact prime_oneHundredThirtyThreeEA_7488998344362023941087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22463070797953626122715870413) ^ 11231535398976813061357935206 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 976655252084940266205037844 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 688987847681306202580004 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22463070797953626122715870413) ^ 2999476 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_52413831861891794286337030963 : Nat.Prime 52413831861891794286337030963 := by
  apply lucas_primality 52413831861891794286337030963 (2 : ZMod 52413831861891794286337030963)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (41, 1), (729266362999, 1), (9424600020163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (41, 1), (729266362999, 1), (9424600020163, 1)] : List FactorBlock).map factorBlockValue).prod) = 52413831861891794286337030963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_31
      · exact prime_oneHundredThirtyThreeEA_41
      · exact prime_oneHundredThirtyThreeEA_729266362999
      · exact prime_oneHundredThirtyThreeEA_9424600020163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 52413831861891794286337030963) ^ 26206915930945897143168515481 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52413831861891794286337030963) ^ 17471277287297264762112343654 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52413831861891794286337030963) ^ 1690768769738444976978613902 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52413831861891794286337030963) ^ 1278386142972970592349683682 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52413831861891794286337030963) ^ 71871999753763038 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 52413831861891794286337030963) ^ 5561385284230374 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_78620747792837691429505546411 : Nat.Prime 78620747792837691429505546411 := by
  apply lucas_primality 78620747792837691429505546411 (2 : ZMod 78620747792837691429505546411)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (79, 1), (33173311304994806510339893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (79, 1), (33173311304994806510339893, 1)] : List FactorBlock).map factorBlockValue).prod) = 78620747792837691429505546411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_5
      · exact prime_oneHundredThirtyThreeEA_79
      · exact prime_oneHundredThirtyThreeEA_33173311304994806510339893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78620747792837691429505546411) ^ 39310373896418845714752773205 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78620747792837691429505546411) ^ 26206915930945897143168515470 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78620747792837691429505546411) ^ 15724149558567538285901109282 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78620747792837691429505546411) ^ 995199339149844195310196790 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78620747792837691429505546411) ^ 2370 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyThreeEA_78620747792837691429505546417 : Nat.Prime 78620747792837691429505546417 := by
  apply lucas_primality 78620747792837691429505546417 (10 : ZMod 78620747792837691429505546417)
  · rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (37, 1), (14756146357514581724757047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (37, 1), (14756146357514581724757047, 1)] : List FactorBlock).map factorBlockValue).prod) = 78620747792837691429505546417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyThreeEA_2
      · exact prime_oneHundredThirtyThreeEA_3
      · exact prime_oneHundredThirtyThreeEA_37
      · exact prime_oneHundredThirtyThreeEA_14756146357514581724757047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 78620747792837691429505546417) ^ 39310373896418845714752773208 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 78620747792837691429505546417) ^ 26206915930945897143168515472 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 78620747792837691429505546417) ^ 2124885075482099768365014768 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide
    · change (10 : ZMod 78620747792837691429505546417) ^ 5328 ≠ 1
      rw [← oneHundredThirtyThreeEAFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092800 : Nat.totient 157241495585675382859011092800 = 51073631334074024124291072000 := by
  rw [← show ((([(2, 6), (5, 2), (7, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092800 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_171401, prime_oneHundredThirtyThreeEA_714027719, prime_oneHundredThirtyThreeEA_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092801 : Nat.totient 157241495585675382859011092801 = 157223641436068743210679187652 := by
  rw [← show ((([(8807, 1), (17854149606639648331896343, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092801 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_8807, prime_oneHundredThirtyThreeEA_17854149606639648331896343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092802 : Nat.totient 157241495585675382859011092802 = 52413831861866205292641470912 := by
  rw [← show ((([(2, 1), (3, 1), (2048623959419, 1), (12792448223820593, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092802 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_2048623959419, prime_oneHundredThirtyThreeEA_12792448223820593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092803 : Nat.totient 157241495585675382859011092803 = 156786713998436508332083157448 := by
  rw [← show ((([(359, 1), (9343, 1), (46879866739395374386619, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092803 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_359, prime_oneHundredThirtyThreeEA_9343, prime_oneHundredThirtyThreeEA_46879866739395374386619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092804 : Nat.totient 157241495585675382859011092804 = 76511888052872520895284864000 := by
  rw [← show ((([(2, 2), (41, 1), (401, 1), (95239247, 1), (25105159921701463, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092804 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_41, prime_oneHundredThirtyThreeEA_401, prime_oneHundredThirtyThreeEA_95239247, prime_oneHundredThirtyThreeEA_25105159921701463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092805 : Nat.totient 157241495585675382859011092805 = 83859555439854885142992798720 := by
  rw [← show ((([(3, 2), (5, 1), (32561, 1), (107314132166071464402889, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092805 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_32561, prime_oneHundredThirtyThreeEA_107314132166071464402889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092806 : Nat.totient 157241495585675382859011092806 = 71427384285245037229170860800 := by
  rw [← show ((([(2, 1), (11, 1), (1553, 1), (4602279915286407037962041, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092806 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_1553, prime_oneHundredThirtyThreeEA_4602279915286407037962041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092807 : Nat.totient 157241495585675382859011092807 = 134685012939426094848884213760 := by
  rw [← show ((([(7, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092807 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_1489, prime_oneHundredThirtyThreeEA_74197, prime_oneHundredThirtyThreeEA_125471, prime_oneHundredThirtyThreeEA_28901293, prime_oneHundredThirtyThreeEA_56069599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092808 : Nat.totient 157241495585675382859011092808 = 52409674077156533535218688000 := by
  rw [← show ((([(2, 3), (3, 1), (13151, 1), (387493, 1), (1416809, 1), (907448481041, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092808 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_13151, prime_oneHundredThirtyThreeEA_387493, prime_oneHundredThirtyThreeEA_1416809, prime_oneHundredThirtyThreeEA_907448481041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092809 : Nat.totient 157241495585675382859011092809 = 152974399323763183018398349440 := by
  rw [← show ((([(47, 1), (167, 1), (20033315783625351364379041, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092809 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_47, prime_oneHundredThirtyThreeEA_167, prime_oneHundredThirtyThreeEA_20033315783625351364379041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092810 : Nat.totient 157241495585675382859011092810 = 62896598234270153143604437120 := by
  rw [← show ((([(2, 1), (5, 1), (15724149558567538285901109281, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092810 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_15724149558567538285901109281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092811 : Nat.totient 157241495585675382859011092811 = 98638779574438195865407488000 := by
  rw [← show ((([(3, 1), (17, 1), (11497, 1), (14009, 1), (14251, 1), (35298853, 1), (38053919, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092811 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_11497, prime_oneHundredThirtyThreeEA_14009, prime_oneHundredThirtyThreeEA_14251, prime_oneHundredThirtyThreeEA_35298853, prime_oneHundredThirtyThreeEA_38053919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092812 : Nat.totient 157241495585675382859011092812 = 72572982035245670944430899200 := by
  rw [← show ((([(2, 2), (13, 1), (4558633, 1), (11730422401, 1), (56547777607, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092812 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_4558633, prime_oneHundredThirtyThreeEA_11730422401, prime_oneHundredThirtyThreeEA_56547777607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092813 : Nat.totient 157241495585675382859011092813 = 157240476458559027869531212800 := by
  rw [← show ((([(154291, 1), (37588625663, 1), (27112534959361, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092813 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_154291, prime_oneHundredThirtyThreeEA_37588625663, prime_oneHundredThirtyThreeEA_27112534959361]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092814 : Nat.totient 157241495585675382859011092814 = 44698566534460132964507712000 := by
  rw [← show ((([(2, 1), (3, 2), (7, 2), (277, 1), (743, 1), (9091, 1), (201451, 1), (472986682277, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092814 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_277, prime_oneHundredThirtyThreeEA_743, prime_oneHundredThirtyThreeEA_9091, prime_oneHundredThirtyThreeEA_201451, prime_oneHundredThirtyThreeEA_472986682277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092815 : Nat.totient 157241495585675382859011092815 = 119090801991795152455960657920 := by
  rw [← show ((([(5, 1), (23, 1), (157, 1), (257, 1), (78031, 1), (434279548061398199, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092815 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_23, prime_oneHundredThirtyThreeEA_157, prime_oneHundredThirtyThreeEA_257, prime_oneHundredThirtyThreeEA_78031, prime_oneHundredThirtyThreeEA_434279548061398199]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092816 : Nat.totient 157241495585675382859011092816 = 78604700829875584454297370240 := by
  rw [← show ((([(2, 4), (5237, 1), (75991, 1), (24694625805007836103, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092816 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5237, prime_oneHundredThirtyThreeEA_75991, prime_oneHundredThirtyThreeEA_24694625805007836103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092817 : Nat.totient 157241495585675382859011092817 = 95297876112527068455043883280 := by
  rw [← show ((([(3, 1), (11, 1), (34263212775643, 1), (139067338396643, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092817 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_34263212775643, prime_oneHundredThirtyThreeEA_139067338396643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092818 : Nat.totient 157241495585675382859011092818 = 76138365617677929552903022080 := by
  rw [← show ((([(2, 1), (59, 1), (131, 1), (137, 1), (74249459371272750773233, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092818 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_59, prime_oneHundredThirtyThreeEA_131, prime_oneHundredThirtyThreeEA_137, prime_oneHundredThirtyThreeEA_74249459371272750773233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092819 : Nat.totient 157241495585675382859011092819 = 148965627395997280131335542656 := by
  rw [← show ((([(19, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092819 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_155440836073, prime_oneHundredThirtyThreeEA_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092820 : Nat.totient 157241495585675382859011092820 = 41400292508633518524904185216 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (79, 1), (33173311304994806510339893, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092820 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_79, prime_oneHundredThirtyThreeEA_33173311304994806510339893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092821 : Nat.totient 157241495585675382859011092821 = 129791124270076108063002132480 := by
  rw [← show ((([(7, 1), (29, 1), (383, 1), (101080961, 1), (20007968354627489, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092821 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_29, prime_oneHundredThirtyThreeEA_383, prime_oneHundredThirtyThreeEA_101080961, prime_oneHundredThirtyThreeEA_20007968354627489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092822 : Nat.totient 157241495585675382859011092822 = 78620747792837691429505546410 := by
  rw [← show ((([(2, 1), (78620747792837691429505546411, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092822 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_78620747792837691429505546411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092823 : Nat.totient 157241495585675382859011092823 = 104433370826045825254244222592 := by
  rw [← show ((([(3, 3), (269, 1), (29077, 1), (103687, 1), (7180872508276979, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092823 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_269, prime_oneHundredThirtyThreeEA_29077, prime_oneHundredThirtyThreeEA_103687, prime_oneHundredThirtyThreeEA_7180872508276979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092824 : Nat.totient 157241495585675382859011092824 = 74033612246409225853766400000 := by
  rw [← show ((([(2, 3), (31, 1), (83, 1), (101, 1), (191, 1), (317021, 1), (417187, 1), (2994083123, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092824 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_31, prime_oneHundredThirtyThreeEA_83, prime_oneHundredThirtyThreeEA_101, prime_oneHundredThirtyThreeEA_191, prime_oneHundredThirtyThreeEA_317021, prime_oneHundredThirtyThreeEA_417187, prime_oneHundredThirtyThreeEA_2994083123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092825 : Nat.totient 157241495585675382859011092825 = 115819809794028456676886476800 := by
  rw [← show ((([(5, 2), (13, 2), (487, 1), (1979, 1), (1205241209, 1), (32039942261, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092825 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_487, prime_oneHundredThirtyThreeEA_1979, prime_oneHundredThirtyThreeEA_1205241209, prime_oneHundredThirtyThreeEA_32039942261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092826 : Nat.totient 157241495585675382859011092826 = 51668309032056545738552328560 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1), (7079, 1), (52141756178154185745119, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092826 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_71, prime_oneHundredThirtyThreeEA_7079, prime_oneHundredThirtyThreeEA_52141756178154185745119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092827 : Nat.totient 157241495585675382859011092827 = 157241182610598133694718432016 := by
  rw [← show ((([(502409, 1), (312975077249164292158403, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092827 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_502409, prime_oneHundredThirtyThreeEA_312975077249164292158403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092828 : Nat.totient 157241495585675382859011092828 = 57369474044744245677181532160 := by
  rw [← show ((([(2, 2), (7, 1), (11, 2), (17, 1), (199, 1), (193897349, 1), (70753820440643, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092828 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_199, prime_oneHundredThirtyThreeEA_193897349, prime_oneHundredThirtyThreeEA_70753820440643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092829 : Nat.totient 157241495585675382859011092829 = 104696222344880534284633248000 := by
  rw [← show ((([(3, 1), (853, 1), (12251, 1), (57371477, 1), (87423725448053, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092829 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_853, prime_oneHundredThirtyThreeEA_12251, prime_oneHundredThirtyThreeEA_57371477, prime_oneHundredThirtyThreeEA_87423725448053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092830 : Nat.totient 157241495585675382859011092830 = 62430988133775591313615609600 := by
  rw [← show ((([(2, 1), (5, 1), (239, 1), (311, 1), (59417, 1), (3560394780600186131, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092830 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_239, prime_oneHundredThirtyThreeEA_311, prime_oneHundredThirtyThreeEA_59417, prime_oneHundredThirtyThreeEA_3560394780600186131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092831 : Nat.totient 157241495585675382859011092831 = 155087244909683164071705807360 := by
  rw [← show ((([(73, 1), (602081, 1), (3577580242882155842887, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092831 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_73, prime_oneHundredThirtyThreeEA_602081, prime_oneHundredThirtyThreeEA_3577580242882155842887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092832 : Nat.totient 157241495585675382859011092832 = 50997241811570394440760350976 := by
  rw [← show ((([(2, 5), (3, 2), (37, 1), (14756146357514581724757047, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092832 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_37, prime_oneHundredThirtyThreeEA_14756146357514581724757047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092833 : Nat.totient 157241495585675382859011092833 = 153584716618566653025080602260 := by
  rw [← show ((([(43, 1), (3656778967108729833930490531, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092833 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_43, prime_oneHundredThirtyThreeEA_3656778967108729833930490531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092834 : Nat.totient 157241495585675382859011092834 = 78620747792837691429505546416 := by
  rw [← show ((([(2, 1), (78620747792837691429505546417, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092834 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_78620747792837691429505546417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092835 : Nat.totient 157241495585675382859011092835 = 71881826553451603592690785248 := by
  rw [← show ((([(3, 1), (5, 1), (7, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092835 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_1497538053196908408181058027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092836 : Nat.totient 157241495585675382859011092836 = 78603843535316292845507167200 := by
  rw [← show ((([(2, 2), (4651, 1), (383238773, 1), (22054204334505983, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092836 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_4651, prime_oneHundredThirtyThreeEA_383238773, prime_oneHundredThirtyThreeEA_22054204334505983]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092837 : Nat.totient 157241495585675382859011092837 = 154487410657056133094207024640 := by
  rw [← show ((([(61, 1), (877, 1), (132887578169, 1), (22118381824309, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092837 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_61, prime_oneHundredThirtyThreeEA_877, prime_oneHundredThirtyThreeEA_132887578169, prime_oneHundredThirtyThreeEA_22118381824309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092838 : Nat.totient 157241495585675382859011092838 = 43842726457966873164702256128 := by
  rw [← show ((([(2, 1), (3, 1), (13, 1), (19, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092838 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_23, prime_oneHundredThirtyThreeEA_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092839 : Nat.totient 157241495585675382859011092839 = 140249704467497768587797200640 := by
  rw [← show ((([(11, 1), (53, 1), (269710970129803401130379233, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092839 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_53, prime_oneHundredThirtyThreeEA_269710970129803401130379233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092840 : Nat.totient 157241495585675382859011092840 = 62864964976733418721364149248 := by
  rw [← show ((([(2, 3), (5, 1), (2027, 1), (104107, 1), (18628311609451359889, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092840 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_2027, prime_oneHundredThirtyThreeEA_104107, prime_oneHundredThirtyThreeEA_18628311609451359889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092841 : Nat.totient 157241495585675382859011092841 = 104827663723783588572674061888 := by
  rw [← show ((([(3, 2), (17471277287297264762112343649, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092841 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_17471277287297264762112343649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092842 : Nat.totient 157241495585675382859011092842 = 67389018770373696850268505600 := by
  rw [← show ((([(2, 1), (7, 1), (352333, 1), (28581281, 1), (1115331887063311, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092842 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_352333, prime_oneHundredThirtyThreeEA_28581281, prime_oneHundredThirtyThreeEA_1115331887063311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092843 : Nat.totient 157241495585675382859011092843 = 157241495584200386910645018240 := by
  rw [← show ((([(106604704321, 1), (1474995841761370283, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092843 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_106604704321, prime_oneHundredThirtyThreeEA_1474995841761370283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092844 : Nat.totient 157241495585675382859011092844 = 52405968679452575157215131200 := by
  rw [← show ((([(2, 2), (3, 1), (8699, 1), (28591, 1), (10708471, 1), (4919939684483, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092844 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_8699, prime_oneHundredThirtyThreeEA_28591, prime_oneHundredThirtyThreeEA_10708471, prime_oneHundredThirtyThreeEA_4919939684483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092845 : Nat.totient 157241495585675382859011092845 = 115505932981086494275962931200 := by
  rw [← show ((([(5, 1), (17, 1), (41, 1), (7702571, 1), (5857720873778091187, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092845 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_41, prime_oneHundredThirtyThreeEA_7702571, prime_oneHundredThirtyThreeEA_5857720873778091187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092846 : Nat.totient 157241495585675382859011092846 = 78620742857517095887363023640 := by
  rw [← show ((([(2, 1), (15930221, 1), (4935320595542126592563, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092846 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_15930221, prime_oneHundredThirtyThreeEA_4935320595542126592563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092847 : Nat.totient 157241495585675382859011092847 = 104778471489252015141868839840 := by
  rw [← show ((([(3, 1), (2131, 1), (225980453, 1), (108840765245108443, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092847 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_2131, prime_oneHundredThirtyThreeEA_225980453, prime_oneHundredThirtyThreeEA_108840765245108443]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092848 : Nat.totient 157241495585675382859011092848 = 78620747789350717461273214400 := by
  rw [← show ((([(2, 4), (22546985603, 1), (435871723482055901, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092848 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_22546985603, prime_oneHundredThirtyThreeEA_435871723482055901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092849 : Nat.totient 157241495585675382859011092849 = 134766695745446260978159543440 := by
  rw [← show ((([(7, 1), (11491, 1), (1954840379249293022601677, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092849 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_11491, prime_oneHundredThirtyThreeEA_1954840379249293022601677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092850 : Nat.totient 157241495585675382859011092850 = 36391161060251877319292160000 := by
  rw [← show ((([(2, 1), (3, 3), (5, 2), (11, 1), (29, 1), (89, 1), (4102538900190732922901, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092850 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_29, prime_oneHundredThirtyThreeEA_89, prime_oneHundredThirtyThreeEA_4102538900190732922901]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092851 : Nat.totient 157241495585675382859011092851 = 143216342531072540998287667200 := by
  rw [← show ((([(13, 1), (113, 1), (223, 1), (2977087, 1), (16813801, 1), (9589215479, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092851 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_113, prime_oneHundredThirtyThreeEA_223, prime_oneHundredThirtyThreeEA_2977087, prime_oneHundredThirtyThreeEA_16813801, prime_oneHundredThirtyThreeEA_9589215479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092852 : Nat.totient 157241495585675382859011092852 = 78452395013838038985331015416 := by
  rw [← show ((([(2, 2), (467, 1), (84176389499826222087265039, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092852 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_467, prime_oneHundredThirtyThreeEA_84176389499826222087265039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092853 : Nat.totient 157241495585675382859011092853 = 103999665238913515000430592000 := by
  rw [← show ((([(3, 1), (193, 1), (503, 1), (1471, 1), (15361, 1), (117021139, 1), (204185141, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092853 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_193, prime_oneHundredThirtyThreeEA_503, prime_oneHundredThirtyThreeEA_1471, prime_oneHundredThirtyThreeEA_15361, prime_oneHundredThirtyThreeEA_117021139, prime_oneHundredThirtyThreeEA_204185141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092854 : Nat.totient 157241495585675382859011092854 = 78599607500341633970126810376 := by
  rw [← show ((([(2, 1), (3719, 1), (21140292496057459378732333, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092854 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3719, prime_oneHundredThirtyThreeEA_21140292496057459378732333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092855 : Nat.totient 157241495585675382859011092855 = 121735245342000599584620566400 := by
  rw [← show ((([(5, 1), (31, 1), (2115703, 1), (2507927, 1), (191190308885861, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092855 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_31, prime_oneHundredThirtyThreeEA_2115703, prime_oneHundredThirtyThreeEA_2507927, prime_oneHundredThirtyThreeEA_191190308885861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092856 : Nat.totient 157241495585675382859011092856 = 43890783864968268320956416000 := by
  rw [← show ((([(2, 3), (3, 1), (7, 1), (47, 1), (563, 1), (40771, 1), (283277, 1), (299281, 1), (10233161, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092856 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_47, prime_oneHundredThirtyThreeEA_563, prime_oneHundredThirtyThreeEA_40771, prime_oneHundredThirtyThreeEA_283277, prime_oneHundredThirtyThreeEA_299281, prime_oneHundredThirtyThreeEA_10233161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092857 : Nat.totient 157241495585675382859011092857 = 148965623123545773665646999984 := by
  rw [← show ((([(19, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092857 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_34858727, prime_oneHundredThirtyThreeEA_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092858 : Nat.totient 157241495585675382859011092858 = 78598226810943438295323501820 := by
  rw [← show ((([(2, 1), (3491, 1), (22520981894253134182041119, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092858 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3491, prime_oneHundredThirtyThreeEA_22520981894253134182041119]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092859 : Nat.totient 157241495585675382859011092859 = 104486364642209985861457920000 := by
  rw [← show ((([(3, 2), (317, 1), (9851, 1), (22269101, 1), (251236300778753, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092859 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_317, prime_oneHundredThirtyThreeEA_9851, prime_oneHundredThirtyThreeEA_22269101, prime_oneHundredThirtyThreeEA_251236300778753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092860 : Nat.totient 157241495585675382859011092860 = 62715340026102227630222289024 := by
  rw [← show ((([(2, 2), (5, 1), (347, 1), (22657276020990689172768169, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092860 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_347, prime_oneHundredThirtyThreeEA_22657276020990689172768169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092861 : Nat.totient 157241495585675382859011092861 = 136731734324522171563457467200 := by
  rw [← show ((([(11, 1), (23, 1), (141343861, 1), (4397133934882509917, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092861 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_23, prime_oneHundredThirtyThreeEA_141343861, prime_oneHundredThirtyThreeEA_4397133934882509917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092862 : Nat.totient 157241495585675382859011092862 = 48495338112660381553206435840 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (67, 1), (491, 1), (618997, 1), (75704580130795409, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092862 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_67, prime_oneHundredThirtyThreeEA_491, prime_oneHundredThirtyThreeEA_618997, prime_oneHundredThirtyThreeEA_75704580130795409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092863 : Nat.totient 157241495585675382859011092863 = 134740608265462183270475683200 := by
  rw [← show ((([(7, 2), (7817, 1), (9887, 1), (19403, 1), (2139920090441051, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092863 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_7817, prime_oneHundredThirtyThreeEA_9887, prime_oneHundredThirtyThreeEA_19403, prime_oneHundredThirtyThreeEA_2139920090441051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092864 : Nat.totient 157241495585675382859011092864 = 72565868269456375318599942144 := by
  rw [← show ((([(2, 7), (13, 1), (10267, 1), (1187189, 1), (7752654287094377, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092864 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_10267, prime_oneHundredThirtyThreeEA_1187189, prime_oneHundredThirtyThreeEA_7752654287094377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092865 : Nat.totient 157241495585675382859011092865 = 83852004598210479237466874112 := by
  rw [← show ((([(3, 1), (5, 1), (8293, 1), (6465527, 1), (85992383, 1), (2273528107, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092865 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_8293, prime_oneHundredThirtyThreeEA_6465527, prime_oneHundredThirtyThreeEA_85992383, prime_oneHundredThirtyThreeEA_2273528107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092866 : Nat.totient 157241495585675382859011092866 = 78620747788746881346264489348 := by
  rw [← show ((([(2, 1), (19218870239, 1), (4090810064022186847, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092866 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_19218870239, prime_oneHundredThirtyThreeEA_4090810064022186847]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092867 : Nat.totient 157241495585675382859011092867 = 156273673916783065255499511648 := by
  rw [← show ((([(163, 1), (49613, 1), (19443931067650780582693, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092867 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_163, prime_oneHundredThirtyThreeEA_49613, prime_oneHundredThirtyThreeEA_19443931067650780582693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092868 : Nat.totient 157241495585675382859011092868 = 52013191943169891353243520000 := by
  rw [← show ((([(2, 2), (3, 2), (229, 1), (631, 1), (691, 1), (4507, 1), (24631, 1), (394050764021, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092868 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_229, prime_oneHundredThirtyThreeEA_631, prime_oneHundredThirtyThreeEA_691, prime_oneHundredThirtyThreeEA_4507, prime_oneHundredThirtyThreeEA_24631, prime_oneHundredThirtyThreeEA_394050764021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092869 : Nat.totient 157241495585675382859011092869 = 152973983149493195245819859856 := by
  rw [← show ((([(37, 1), (8623, 1), (492841256055224346135919, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092869 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_37, prime_oneHundredThirtyThreeEA_8623, prime_oneHundredThirtyThreeEA_492841256055224346135919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092870 : Nat.totient 157241495585675382859011092870 = 53911369915088702694518088960 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (2246307079795362612271587041, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092870 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_2246307079795362612271587041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092871 : Nat.totient 157241495585675382859011092871 = 104545806618488562840384927200 := by
  rw [← show ((([(3, 1), (887, 1), (1151, 1), (1439, 1), (35676823002993275099, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092871 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_887, prime_oneHundredThirtyThreeEA_1151, prime_oneHundredThirtyThreeEA_1439, prime_oneHundredThirtyThreeEA_35676823002993275099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092872 : Nat.totient 157241495585675382859011092872 = 71456906091150228003310771200 := by
  rw [← show ((([(2, 3), (11, 1), (5659, 1), (18481, 1), (16871527, 1), (1012662998143, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092872 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_5659, prime_oneHundredThirtyThreeEA_18481, prime_oneHundredThirtyThreeEA_16871527, prime_oneHundredThirtyThreeEA_1012662998143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092873 : Nat.totient 157241495585675382859011092873 = 156836197186673205970702016832 := by
  rw [← show ((([(389, 1), (145637, 1), (91686379, 1), (30271993327859, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092873 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_389, prime_oneHundredThirtyThreeEA_145637, prime_oneHundredThirtyThreeEA_91686379, prime_oneHundredThirtyThreeEA_30271993327859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092874 : Nat.totient 157241495585675382859011092874 = 51896622091800557726428000896 := by
  rw [← show ((([(2, 1), (3, 1), (103, 1), (6547, 1), (126713, 1), (306700989194377763, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092874 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_103, prime_oneHundredThirtyThreeEA_6547, prime_oneHundredThirtyThreeEA_126713, prime_oneHundredThirtyThreeEA_306700989194377763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092875 : Nat.totient 157241495585675382859011092875 = 125793196468532682607383840000 := by
  rw [← show ((([(5, 3), (24151281055201, 1), (52085517195143, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092875 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_24151281055201, prime_oneHundredThirtyThreeEA_52085517195143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092876 : Nat.totient 157241495585675382859011092876 = 72750636026700661745421189120 := by
  rw [← show ((([(2, 2), (19, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092876 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_43, prime_oneHundredThirtyThreeEA_4282273, prime_oneHundredThirtyThreeEA_32701811, prime_oneHundredThirtyThreeEA_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092877 : Nat.totient 157241495585675382859011092877 = 81534227130748400820098515200 := by
  rw [← show ((([(3, 5), (7, 1), (13, 1), (59, 1), (143141, 1), (841983229614766891, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092877 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_59, prime_oneHundredThirtyThreeEA_143141, prime_oneHundredThirtyThreeEA_841983229614766891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092878 : Nat.totient 157241495585675382859011092878 = 78620747755610064633049968624 := by
  rw [← show ((([(2, 1), (2111892553, 1), (37227626794343685263, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092878 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_2111892553, prime_oneHundredThirtyThreeEA_37227626794343685263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092879 : Nat.totient 157241495585675382859011092879 = 142541963620014953747270246400 := by
  rw [← show ((([(17, 1), (29, 1), (421, 1), (21661, 1), (171023, 1), (3593003, 1), (56917727, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092879 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_29, prime_oneHundredThirtyThreeEA_421, prime_oneHundredThirtyThreeEA_21661, prime_oneHundredThirtyThreeEA_171023, prime_oneHundredThirtyThreeEA_3593003, prime_oneHundredThirtyThreeEA_56917727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092880 : Nat.totient 157241495585675382859011092880 = 41675336205161168900090265600 := by
  rw [← show ((([(2, 4), (3, 1), (5, 1), (197, 1), (1109, 1), (7919, 1), (378693463456599601, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092880 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_197, prime_oneHundredThirtyThreeEA_1109, prime_oneHundredThirtyThreeEA_7919, prime_oneHundredThirtyThreeEA_378693463456599601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092881 : Nat.totient 157241495585675382859011092881 = 157162805249169794813583590928 := by
  rw [← show ((([(2087, 1), (46957, 1), (1604517189111352187459, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092881 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2087, prime_oneHundredThirtyThreeEA_46957, prime_oneHundredThirtyThreeEA_1604517189111352187459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092882 : Nat.totient 157241495585675382859011092882 = 78595525113239445502389103360 := by
  rw [← show ((([(2, 1), (3119, 1), (6830777, 1), (19001417, 1), (194207366471, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092882 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3119, prime_oneHundredThirtyThreeEA_6830777, prime_oneHundredThirtyThreeEA_19001417, prime_oneHundredThirtyThreeEA_194207366471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092883 : Nat.totient 157241495585675382859011092883 = 95297870700699092866212927840 := by
  rw [← show ((([(3, 1), (11, 1), (17609173, 1), (270591572109975110887, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092883 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_17609173, prime_oneHundredThirtyThreeEA_270591572109975110887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092884 : Nat.totient 157241495585675382859011092884 = 64457269542043145995203443808 := by
  rw [← show ((([(2, 2), (7, 1), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092884 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_23, prime_oneHundredThirtyThreeEA_32603, prime_oneHundredThirtyThreeEA_7488998344362023941087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092885 : Nat.totient 157241495585675382859011092885 = 125383446576578114321760058176 := by
  rw [← show ((([(5, 1), (307, 1), (1890247399, 1), (54192618628544989, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092885 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_307, prime_oneHundredThirtyThreeEA_1890247399, prime_oneHundredThirtyThreeEA_54192618628544989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092886 : Nat.totient 157241495585675382859011092886 = 49485915211783818317512867200 := by
  rw [← show ((([(2, 1), (3, 2), (31, 1), (41, 1), (729266362999, 1), (9424600020163, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092886 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_31, prime_oneHundredThirtyThreeEA_41, prime_oneHundredThirtyThreeEA_729266362999, prime_oneHundredThirtyThreeEA_9424600020163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092887 : Nat.totient 157241495585675382859011092887 = 157230194866825004177826724992 := by
  rw [← show ((([(13933, 1), (10361777, 1), (1089151483564018307, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092887 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_13933, prime_oneHundredThirtyThreeEA_10361777, prime_oneHundredThirtyThreeEA_1089151483564018307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092888 : Nat.totient 157241495585675382859011092888 = 78619119056167789465770823200 := by
  rw [← show ((([(2, 3), (48271, 1), (407184167475490933632541, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092888 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_48271, prime_oneHundredThirtyThreeEA_407184167475490933632541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092889 : Nat.totient 157241495585675382859011092889 = 104827663723783588572674061924 := by
  rw [← show ((([(3, 1), (52413831861891794286337030963, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092889 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_52413831861891794286337030963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092890 : Nat.totient 157241495585675382859011092890 = 57354126636692816893283328000 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (151, 1), (181, 1), (56659, 1), (453833, 1), (1721088942029, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092890 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_13, prime_oneHundredThirtyThreeEA_151, prime_oneHundredThirtyThreeEA_181, prime_oneHundredThirtyThreeEA_56659, prime_oneHundredThirtyThreeEA_453833, prime_oneHundredThirtyThreeEA_1721088942029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092891 : Nat.totient 157241495585675382859011092891 = 134778424787721756736295222472 := by
  rw [← show ((([(7, 1), (22463070797953626122715870413, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092891 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_22463070797953626122715870413]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092892 : Nat.totient 157241495585675382859011092892 = 51273109678193453067389299200 := by
  rw [← show ((([(2, 2), (3, 1), (53, 1), (521, 1), (967, 1), (490733665773440592071, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092892 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_53, prime_oneHundredThirtyThreeEA_521, prime_oneHundredThirtyThreeEA_967, prime_oneHundredThirtyThreeEA_490733665773440592071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092893 : Nat.totient 157241495585675382859011092893 = 157219006585468288502962294704 := by
  rw [← show ((([(10243, 1), (22027, 1), (696922749607807983613, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092893 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_10243, prime_oneHundredThirtyThreeEA_22027, prime_oneHundredThirtyThreeEA_696922749607807983613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092894 : Nat.totient 157241495585675382859011092894 = 71473100485535165429142748800 := by
  rw [← show ((([(2, 1), (11, 1), (233117, 1), (30659886273587040541681, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092894 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_11, prime_oneHundredThirtyThreeEA_233117, prime_oneHundredThirtyThreeEA_30659886273587040541681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092895 : Nat.totient 157241495585675382859011092895 = 79447798389252482249494579200 := by
  rw [← show ((([(3, 2), (5, 1), (19, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092895 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_19, prime_oneHundredThirtyThreeEA_148193, prime_oneHundredThirtyThreeEA_732506743, prime_oneHundredThirtyThreeEA_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092896 : Nat.totient 157241495585675382859011092896 = 73233152379546972225227882496 := by
  rw [← show ((([(2, 5), (17, 1), (97, 1), (359488603, 1), (8289176853448999, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092896 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_17, prime_oneHundredThirtyThreeEA_97, prime_oneHundredThirtyThreeEA_359488603, prime_oneHundredThirtyThreeEA_8289176853448999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092897 : Nat.totient 157241495585675382859011092897 = 153426370701046962984371639040 := by
  rw [← show ((([(71, 1), (107, 1), (1013, 1), (20432221788810149231377, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092897 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_71, prime_oneHundredThirtyThreeEA_107, prime_oneHundredThirtyThreeEA_1013, prime_oneHundredThirtyThreeEA_20432221788810149231377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092898 : Nat.totient 157241495585675382859011092898 = 44189646536662531327401984000 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (61, 1), (47275729, 1), (1298224515520902401, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092898 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_7, prime_oneHundredThirtyThreeEA_61, prime_oneHundredThirtyThreeEA_47275729, prime_oneHundredThirtyThreeEA_1298224515520902401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092899 : Nat.totient 157241495585675382859011092899 = 155251096907375694468390699240 := by
  rw [← show ((([(79, 1), (1990398678299688390620393581, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092899 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_79, prime_oneHundredThirtyThreeEA_1990398678299688390620393581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092900 : Nat.totient 157241495585675382859011092900 = 62474420031617154056218383360 := by
  rw [← show ((([(2, 2), (5, 2), (149, 1), (1172537, 1), (648508079, 1), (13878385627, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092900 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_2, prime_oneHundredThirtyThreeEA_5, prime_oneHundredThirtyThreeEA_149, prime_oneHundredThirtyThreeEA_1172537, prime_oneHundredThirtyThreeEA_648508079, prime_oneHundredThirtyThreeEA_13878385627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyThreeEA_157241495585675382859011092901 : Nat.totient 157241495585675382859011092901 = 104794709275126371890528798400 := by
  rw [← show ((([(3, 1), (3181, 1), (762026077, 1), (21622823765946191, 1)] : List FactorBlock).map factorBlockValue).prod) = 157241495585675382859011092901 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyThreeEA_3, prime_oneHundredThirtyThreeEA_3181, prime_oneHundredThirtyThreeEA_762026077, prime_oneHundredThirtyThreeEA_21622823765946191]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyThreeEA : certifiedKill 1 157241495585675382859011092799 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092800, phi_oneHundredThirtyThreeEA_157241495585675382859011092801, phi_oneHundredThirtyThreeEA_157241495585675382859011092802,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092803, phi_oneHundredThirtyThreeEA_157241495585675382859011092804, phi_oneHundredThirtyThreeEA_157241495585675382859011092805,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092806, phi_oneHundredThirtyThreeEA_157241495585675382859011092807, phi_oneHundredThirtyThreeEA_157241495585675382859011092808,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092809, phi_oneHundredThirtyThreeEA_157241495585675382859011092810, phi_oneHundredThirtyThreeEA_157241495585675382859011092811,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092812, phi_oneHundredThirtyThreeEA_157241495585675382859011092813, phi_oneHundredThirtyThreeEA_157241495585675382859011092814,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092815, phi_oneHundredThirtyThreeEA_157241495585675382859011092816, phi_oneHundredThirtyThreeEA_157241495585675382859011092817,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092818, phi_oneHundredThirtyThreeEA_157241495585675382859011092819, phi_oneHundredThirtyThreeEA_157241495585675382859011092820,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092821, phi_oneHundredThirtyThreeEA_157241495585675382859011092822, phi_oneHundredThirtyThreeEA_157241495585675382859011092823,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092824, phi_oneHundredThirtyThreeEA_157241495585675382859011092825, phi_oneHundredThirtyThreeEA_157241495585675382859011092826,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092827, phi_oneHundredThirtyThreeEA_157241495585675382859011092828, phi_oneHundredThirtyThreeEA_157241495585675382859011092829,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092830, phi_oneHundredThirtyThreeEA_157241495585675382859011092831, phi_oneHundredThirtyThreeEA_157241495585675382859011092832,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092833, phi_oneHundredThirtyThreeEA_157241495585675382859011092834, phi_oneHundredThirtyThreeEA_157241495585675382859011092835,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092836, phi_oneHundredThirtyThreeEA_157241495585675382859011092837, phi_oneHundredThirtyThreeEA_157241495585675382859011092838,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092839, phi_oneHundredThirtyThreeEA_157241495585675382859011092840, phi_oneHundredThirtyThreeEA_157241495585675382859011092841,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092842, phi_oneHundredThirtyThreeEA_157241495585675382859011092843, phi_oneHundredThirtyThreeEA_157241495585675382859011092844,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092845, phi_oneHundredThirtyThreeEA_157241495585675382859011092846, phi_oneHundredThirtyThreeEA_157241495585675382859011092847,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092848, phi_oneHundredThirtyThreeEA_157241495585675382859011092849, phi_oneHundredThirtyThreeEA_157241495585675382859011092850,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092851, phi_oneHundredThirtyThreeEA_157241495585675382859011092852, phi_oneHundredThirtyThreeEA_157241495585675382859011092853,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092854, phi_oneHundredThirtyThreeEA_157241495585675382859011092855, phi_oneHundredThirtyThreeEA_157241495585675382859011092856,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092857, phi_oneHundredThirtyThreeEA_157241495585675382859011092858, phi_oneHundredThirtyThreeEA_157241495585675382859011092859,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092860, phi_oneHundredThirtyThreeEA_157241495585675382859011092861, phi_oneHundredThirtyThreeEA_157241495585675382859011092862,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092863, phi_oneHundredThirtyThreeEA_157241495585675382859011092864, phi_oneHundredThirtyThreeEA_157241495585675382859011092865,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092866, phi_oneHundredThirtyThreeEA_157241495585675382859011092867, phi_oneHundredThirtyThreeEA_157241495585675382859011092868,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092869, phi_oneHundredThirtyThreeEA_157241495585675382859011092870, phi_oneHundredThirtyThreeEA_157241495585675382859011092871,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092872, phi_oneHundredThirtyThreeEA_157241495585675382859011092873, phi_oneHundredThirtyThreeEA_157241495585675382859011092874,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092875, phi_oneHundredThirtyThreeEA_157241495585675382859011092876, phi_oneHundredThirtyThreeEA_157241495585675382859011092877,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092878, phi_oneHundredThirtyThreeEA_157241495585675382859011092879, phi_oneHundredThirtyThreeEA_157241495585675382859011092880,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092881, phi_oneHundredThirtyThreeEA_157241495585675382859011092882, phi_oneHundredThirtyThreeEA_157241495585675382859011092883,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092884, phi_oneHundredThirtyThreeEA_157241495585675382859011092885, phi_oneHundredThirtyThreeEA_157241495585675382859011092886,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092887, phi_oneHundredThirtyThreeEA_157241495585675382859011092888, phi_oneHundredThirtyThreeEA_157241495585675382859011092889,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092890, phi_oneHundredThirtyThreeEA_157241495585675382859011092891, phi_oneHundredThirtyThreeEA_157241495585675382859011092892,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092893, phi_oneHundredThirtyThreeEA_157241495585675382859011092894, phi_oneHundredThirtyThreeEA_157241495585675382859011092895,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092896, phi_oneHundredThirtyThreeEA_157241495585675382859011092897, phi_oneHundredThirtyThreeEA_157241495585675382859011092898,
    phi_oneHundredThirtyThreeEA_157241495585675382859011092899, phi_oneHundredThirtyThreeEA_157241495585675382859011092900, phi_oneHundredThirtyThreeEA_157241495585675382859011092901
    ]

end TotientTailPeriodKiller
end Erdos249257
