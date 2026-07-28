import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSixtyFiveFGFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSixtyFiveFGFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSixtyFiveFGFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSixtyFiveFGFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSixtyFiveFGFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSixtyFiveFGFastPow a n * oneHundredSixtyFiveFGFastPow a n * a else oneHundredSixtyFiveFGFastPow a n * oneHundredSixtyFiveFGFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSixtyFiveFG_2 : Nat.Prime 2 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3 : Nat.Prime 3 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5 : Nat.Prime 5 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7 : Nat.Prime 7 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11 : Nat.Prime 11 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_13 : Nat.Prime 13 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_17 : Nat.Prime 17 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_19 : Nat.Prime 19 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_23 : Nat.Prime 23 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_29 : Nat.Prime 29 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_31 : Nat.Prime 31 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_37 : Nat.Prime 37 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_41 : Nat.Prime 41 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_43 : Nat.Prime 43 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_47 : Nat.Prime 47 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_53 : Nat.Prime 53 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_59 : Nat.Prime 59 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_61 : Nat.Prime 61 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_67 : Nat.Prime 67 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_71 : Nat.Prime 71 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_73 : Nat.Prime 73 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_79 : Nat.Prime 79 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_83 : Nat.Prime 83 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_89 : Nat.Prime 89 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_97 : Nat.Prime 97 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_101 : Nat.Prime 101 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_103 : Nat.Prime 103 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_107 : Nat.Prime 107 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_109 : Nat.Prime 109 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_113 : Nat.Prime 113 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_127 : Nat.Prime 127 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_131 : Nat.Prime 131 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_137 : Nat.Prime 137 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_139 : Nat.Prime 139 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_149 : Nat.Prime 149 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_151 : Nat.Prime 151 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_157 : Nat.Prime 157 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_163 : Nat.Prime 163 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_167 : Nat.Prime 167 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_173 : Nat.Prime 173 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_179 : Nat.Prime 179 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_181 : Nat.Prime 181 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_191 : Nat.Prime 191 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_193 : Nat.Prime 193 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_197 : Nat.Prime 197 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_199 : Nat.Prime 199 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_211 : Nat.Prime 211 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_223 : Nat.Prime 223 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_227 : Nat.Prime 227 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_229 : Nat.Prime 229 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_239 : Nat.Prime 239 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_257 : Nat.Prime 257 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_271 : Nat.Prime 271 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_281 : Nat.Prime 281 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_283 : Nat.Prime 283 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_311 : Nat.Prime 311 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_337 : Nat.Prime 337 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_347 : Nat.Prime 347 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_349 : Nat.Prime 349 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_353 : Nat.Prime 353 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_359 : Nat.Prime 359 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_367 : Nat.Prime 367 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_373 : Nat.Prime 373 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_389 : Nat.Prime 389 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_397 : Nat.Prime 397 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_401 : Nat.Prime 401 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_409 : Nat.Prime 409 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_419 : Nat.Prime 419 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_431 : Nat.Prime 431 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_433 : Nat.Prime 433 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_439 : Nat.Prime 439 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_443 : Nat.Prime 443 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_449 : Nat.Prime 449 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_457 : Nat.Prime 457 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_461 : Nat.Prime 461 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_463 : Nat.Prime 463 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_467 : Nat.Prime 467 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_487 : Nat.Prime 487 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_491 : Nat.Prime 491 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_509 : Nat.Prime 509 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_523 : Nat.Prime 523 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_541 : Nat.Prime 541 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_557 : Nat.Prime 557 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_571 : Nat.Prime 571 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_577 : Nat.Prime 577 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_593 : Nat.Prime 593 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_599 : Nat.Prime 599 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_613 : Nat.Prime 613 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_617 : Nat.Prime 617 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_641 : Nat.Prime 641 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_643 : Nat.Prime 643 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_661 : Nat.Prime 661 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_683 : Nat.Prime 683 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_691 : Nat.Prime 691 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_709 : Nat.Prime 709 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_733 : Nat.Prime 733 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_743 : Nat.Prime 743 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_769 : Nat.Prime 769 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_787 : Nat.Prime 787 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_811 : Nat.Prime 811 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_823 : Nat.Prime 823 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_829 : Nat.Prime 829 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_853 : Nat.Prime 853 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_857 : Nat.Prime 857 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_877 : Nat.Prime 877 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_881 : Nat.Prime 881 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_911 : Nat.Prime 911 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_929 : Nat.Prime 929 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_947 : Nat.Prime 947 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_953 : Nat.Prime 953 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_977 : Nat.Prime 977 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_991 : Nat.Prime 991 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1031 : Nat.Prime 1031 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1033 : Nat.Prime 1033 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1049 : Nat.Prime 1049 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1093 : Nat.Prime 1093 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1097 : Nat.Prime 1097 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1109 : Nat.Prime 1109 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1117 : Nat.Prime 1117 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1123 : Nat.Prime 1123 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1129 : Nat.Prime 1129 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1171 : Nat.Prime 1171 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1229 : Nat.Prime 1229 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1231 : Nat.Prime 1231 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1237 : Nat.Prime 1237 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1291 : Nat.Prime 1291 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1297 : Nat.Prime 1297 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1321 : Nat.Prime 1321 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1327 : Nat.Prime 1327 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1427 : Nat.Prime 1427 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1451 : Nat.Prime 1451 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1459 : Nat.Prime 1459 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1471 : Nat.Prime 1471 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1523 : Nat.Prime 1523 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1549 : Nat.Prime 1549 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1583 : Nat.Prime 1583 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1697 : Nat.Prime 1697 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1811 : Nat.Prime 1811 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1873 : Nat.Prime 1873 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1901 : Nat.Prime 1901 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1951 : Nat.Prime 1951 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2003 : Nat.Prime 2003 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2063 : Nat.Prime 2063 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2081 : Nat.Prime 2081 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2089 : Nat.Prime 2089 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2099 : Nat.Prime 2099 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2111 : Nat.Prime 2111 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2131 : Nat.Prime 2131 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2287 : Nat.Prime 2287 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2371 : Nat.Prime 2371 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2477 : Nat.Prime 2477 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2531 : Nat.Prime 2531 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2633 : Nat.Prime 2633 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2663 : Nat.Prime 2663 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2711 : Nat.Prime 2711 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2713 : Nat.Prime 2713 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2791 : Nat.Prime 2791 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2803 : Nat.Prime 2803 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2843 : Nat.Prime 2843 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2903 : Nat.Prime 2903 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2939 : Nat.Prime 2939 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2963 : Nat.Prime 2963 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3061 : Nat.Prime 3061 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3067 : Nat.Prime 3067 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3251 : Nat.Prime 3251 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3259 : Nat.Prime 3259 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3323 : Nat.Prime 3323 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3449 : Nat.Prime 3449 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3457 : Nat.Prime 3457 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3461 : Nat.Prime 3461 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3499 : Nat.Prime 3499 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3691 : Nat.Prime 3691 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3727 : Nat.Prime 3727 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3821 : Nat.Prime 3821 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3847 : Nat.Prime 3847 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3863 : Nat.Prime 3863 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3911 : Nat.Prime 3911 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4051 : Nat.Prime 4051 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4241 : Nat.Prime 4241 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4259 : Nat.Prime 4259 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4337 : Nat.Prime 4337 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4373 : Nat.Prime 4373 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4483 : Nat.Prime 4483 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4909 : Nat.Prime 4909 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4931 : Nat.Prime 4931 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5171 : Nat.Prime 5171 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5273 : Nat.Prime 5273 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5387 : Nat.Prime 5387 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5521 : Nat.Prime 5521 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5791 : Nat.Prime 5791 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5807 : Nat.Prime 5807 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5821 : Nat.Prime 5821 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5879 : Nat.Prime 5879 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_6151 : Nat.Prime 6151 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_6803 : Nat.Prime 6803 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_6863 : Nat.Prime 6863 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7229 : Nat.Prime 7229 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7237 : Nat.Prime 7237 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7591 : Nat.Prime 7591 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7829 : Nat.Prime 7829 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7949 : Nat.Prime 7949 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_7993 : Nat.Prime 7993 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8263 : Nat.Prime 8263 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8317 : Nat.Prime 8317 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8573 : Nat.Prime 8573 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_9109 : Nat.Prime 9109 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_9161 : Nat.Prime 9161 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_9491 : Nat.Prime 9491 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10111 : Nat.Prime 10111 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10333 : Nat.Prime 10333 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10357 : Nat.Prime 10357 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11243 : Nat.Prime 11243 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11369 : Nat.Prime 11369 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11437 : Nat.Prime 11437 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11527 : Nat.Prime 11527 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11593 : Nat.Prime 11593 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12157 : Nat.Prime 12157 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12437 : Nat.Prime 12437 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12539 : Nat.Prime 12539 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12601 : Nat.Prime 12601 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12763 : Nat.Prime 12763 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12809 : Nat.Prime 12809 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12823 : Nat.Prime 12823 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12893 : Nat.Prime 12893 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_13159 : Nat.Prime 13159 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_14389 : Nat.Prime 14389 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_14411 : Nat.Prime 14411 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_14437 : Nat.Prime 14437 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_14831 : Nat.Prime 14831 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_15173 : Nat.Prime 15173 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_15269 : Nat.Prime 15269 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16187 : Nat.Prime 16187 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16553 : Nat.Prime 16553 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16703 : Nat.Prime 16703 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16993 : Nat.Prime 16993 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_17117 : Nat.Prime 17117 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_17203 : Nat.Prime 17203 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_18257 : Nat.Prime 18257 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_18541 : Nat.Prime 18541 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_18973 : Nat.Prime 18973 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_19471 : Nat.Prime 19471 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_19577 : Nat.Prime 19577 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_19853 : Nat.Prime 19853 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_19973 : Nat.Prime 19973 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_20023 : Nat.Prime 20023 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_20719 : Nat.Prime 20719 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_20753 : Nat.Prime 20753 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_21269 : Nat.Prime 21269 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_21617 : Nat.Prime 21617 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_22441 : Nat.Prime 22441 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_23017 : Nat.Prime 23017 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_23447 : Nat.Prime 23447 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_24547 : Nat.Prime 24547 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_25117 : Nat.Prime 25117 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_29537 : Nat.Prime 29537 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_31177 : Nat.Prime 31177 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_31277 : Nat.Prime 31277 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_31699 : Nat.Prime 31699 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_32051 : Nat.Prime 32051 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_32083 : Nat.Prime 32083 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_33413 : Nat.Prime 33413 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_33493 : Nat.Prime 33493 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_33721 : Nat.Prime 33721 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_34171 : Nat.Prime 34171 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_35603 : Nat.Prime 35603 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_35863 : Nat.Prime 35863 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_36479 : Nat.Prime 36479 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_36697 : Nat.Prime 36697 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_37489 : Nat.Prime 37489 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_37717 : Nat.Prime 37717 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_40039 : Nat.Prime 40039 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_42589 : Nat.Prime 42589 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_43759 : Nat.Prime 43759 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_44159 : Nat.Prime 44159 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_50123 : Nat.Prime 50123 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_52543 : Nat.Prime 52543 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_53849 : Nat.Prime 53849 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_55373 : Nat.Prime 55373 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_58537 : Nat.Prime 58537 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_59723 : Nat.Prime 59723 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_60029 : Nat.Prime 60029 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_60289 : Nat.Prime 60289 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_61471 : Nat.Prime 61471 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_62401 : Nat.Prime 62401 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_65479 : Nat.Prime 65479 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_66877 : Nat.Prime 66877 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_67181 : Nat.Prime 67181 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_67231 : Nat.Prime 67231 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_71249 : Nat.Prime 71249 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_72211 : Nat.Prime 72211 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_72911 : Nat.Prime 72911 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_74843 : Nat.Prime 74843 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_80077 : Nat.Prime 80077 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_85517 : Nat.Prime 85517 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_87223 : Nat.Prime 87223 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_91121 : Nat.Prime 91121 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_93083 : Nat.Prime 93083 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_98729 : Nat.Prime 98729 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_100271 : Nat.Prime 100271 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_101653 : Nat.Prime 101653 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_103471 : Nat.Prime 103471 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_105239 : Nat.Prime 105239 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_119047 : Nat.Prime 119047 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_124769 : Nat.Prime 124769 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_127321 : Nat.Prime 127321 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_131203 : Nat.Prime 131203 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_144223 : Nat.Prime 144223 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_149173 : Nat.Prime 149173 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_151579 : Nat.Prime 151579 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_151687 : Nat.Prime 151687 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_152597 : Nat.Prime 152597 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_153457 : Nat.Prime 153457 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_161233 : Nat.Prime 161233 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_161977 : Nat.Prime 161977 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_167009 : Nat.Prime 167009 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_171401 : Nat.Prime 171401 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_173897 : Nat.Prime 173897 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_185153 : Nat.Prime 185153 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_187423 : Nat.Prime 187423 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_205721 : Nat.Prime 205721 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_216973 : Nat.Prime 216973 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_223759 : Nat.Prime 223759 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_241643 : Nat.Prime 241643 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_253247 : Nat.Prime 253247 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_264889 : Nat.Prime 264889 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_277813 : Nat.Prime 277813 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_293269 : Nat.Prime 293269 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_330791 : Nat.Prime 330791 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_336827 : Nat.Prime 336827 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_339679 : Nat.Prime 339679 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_344567 : Nat.Prime 344567 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_348181 : Nat.Prime 348181 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_351257 : Nat.Prime 351257 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_353501 : Nat.Prime 353501 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_365419 : Nat.Prime 365419 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_366277 : Nat.Prime 366277 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_371387 : Nat.Prime 371387 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_376583 : Nat.Prime 376583 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_399181 : Nat.Prime 399181 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_405749 : Nat.Prime 405749 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_433439 : Nat.Prime 433439 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_483671 : Nat.Prime 483671 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_487397 : Nat.Prime 487397 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_536563 : Nat.Prime 536563 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_604243 : Nat.Prime 604243 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_607213 : Nat.Prime 607213 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_622247 : Nat.Prime 622247 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_626611 : Nat.Prime 626611 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_670673 : Nat.Prime 670673 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_687023 : Nat.Prime 687023 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_702239 : Nat.Prime 702239 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_758851 : Nat.Prime 758851 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_791773 : Nat.Prime 791773 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_800243 : Nat.Prime 800243 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_847991 : Nat.Prime 847991 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_946123 : Nat.Prime 946123 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1023313 : Nat.Prime 1023313 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1030297 : Nat.Prime 1030297 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1077719 : Nat.Prime 1077719 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1162991 : Nat.Prime 1162991 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1167811 : Nat.Prime 1167811 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1243169 : Nat.Prime 1243169 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1243387 : Nat.Prime 1243387 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1276397 : Nat.Prime 1276397 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1333901 : Nat.Prime 1333901 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1371913 : Nat.Prime 1371913 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1462199 : Nat.Prime 1462199 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1502939 : Nat.Prime 1502939 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1625321 : Nat.Prime 1625321 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1685869 : Nat.Prime 1685869 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_1826549 : Nat.Prime 1826549 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2046487 : Nat.Prime 2046487 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2127409 : Nat.Prime 2127409 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2159147 : Nat.Prime 2159147 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2186603 : Nat.Prime 2186603 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2251129 : Nat.Prime 2251129 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2327173 : Nat.Prime 2327173 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2404357 : Nat.Prime 2404357 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2444899 : Nat.Prime 2444899 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2492701 : Nat.Prime 2492701 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2668993 : Nat.Prime 2668993 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2684477 : Nat.Prime 2684477 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_2880121 : Nat.Prime 2880121 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3092989 : Nat.Prime 3092989 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3110213 : Nat.Prime 3110213 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3148051 : Nat.Prime 3148051 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3165203 : Nat.Prime 3165203 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3283807 : Nat.Prime 3283807 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3599009 : Nat.Prime 3599009 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3700691 : Nat.Prime 3700691 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_3755669 : Nat.Prime 3755669 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4015201 : Nat.Prime 4015201 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4174343 : Nat.Prime 4174343 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4253537 : Nat.Prime 4253537 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4362719 : Nat.Prime 4362719 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4514947 : Nat.Prime 4514947 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4631749 : Nat.Prime 4631749 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4663781 : Nat.Prime 4663781 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_4671071 : Nat.Prime 4671071 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5247019 : Nat.Prime 5247019 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5351669 : Nat.Prime 5351669 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5601787 : Nat.Prime 5601787 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_5760091 : Nat.Prime 5760091 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_6007159 : Nat.Prime 6007159 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_6181057 : Nat.Prime 6181057 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8095547 : Nat.Prime 8095547 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8199473 : Nat.Prime 8199473 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8225573 : Nat.Prime 8225573 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8348687 : Nat.Prime 8348687 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8372717 : Nat.Prime 8372717 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_8420653 : Nat.Prime 8420653 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_9173893 : Nat.Prime 9173893 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_9312211 : Nat.Prime 9312211 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10362637 : Nat.Prime 10362637 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10820141 : Nat.Prime 10820141 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_10916527 : Nat.Prime 10916527 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_11352647 : Nat.Prime 11352647 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12292349 : Nat.Prime 12292349 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12753577 : Nat.Prime 12753577 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_12924887 : Nat.Prime 12924887 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_13617913 : Nat.Prime 13617913 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_14078959 : Nat.Prime 14078959 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_15121543 : Nat.Prime 15121543 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_15674389 : Nat.Prime 15674389 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_15967703 : Nat.Prime 15967703 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16120057 : Nat.Prime 16120057 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_16356083 : Nat.Prime 16356083 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_17305033 : Nat.Prime 17305033 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_18601013 : Nat.Prime 18601013 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_23740417 : Nat.Prime 23740417 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_24455819 : Nat.Prime 24455819 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_24910663 : Nat.Prime 24910663 := by
  norm_num

private theorem prime_oneHundredSixtyFiveFG_30520993 : Nat.Prime 30520993 := by
  apply lucas_primality 30520993 (7 : ZMod 30520993)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (29, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (29, 1), (577, 1)] : List FactorBlock).map factorBlockValue).prod) = 30520993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 30520993) ^ 15260496 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 10173664 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 1606368 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 1052448 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 30520993) ^ 52896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_30612443 : Nat.Prime 30612443 := by
  apply lucas_primality 30612443 (2 : ZMod 30612443)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2186603, 1)] : List FactorBlock).map factorBlockValue).prod) = 30612443 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_2186603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30612443) ^ 15306221 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 4373206 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 30612443) ^ 14 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_31100039 : Nat.Prime 31100039 := by
  apply lucas_primality 31100039 (11 : ZMod 31100039)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (641, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (641, 1), (1427, 1)] : List FactorBlock).map factorBlockValue).prod) = 31100039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_641
      · exact prime_oneHundredSixtyFiveFG_1427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 31100039) ^ 15550019 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31100039) ^ 1829414 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31100039) ^ 48518 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 31100039) ^ 21794 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_31922287 : Nat.Prime 31922287 := by
  apply lucas_primality 31922287 (3 : ZMod 31922287)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (483671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (483671, 1)] : List FactorBlock).map factorBlockValue).prod) = 31922287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_483671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 31922287) ^ 15961143 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922287) ^ 10640762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922287) ^ 2902026 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 31922287) ^ 66 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_37322557 : Nat.Prime 37322557 := by
  apply lucas_primality 37322557 (2 : ZMod 37322557)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3110213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3110213, 1)] : List FactorBlock).map factorBlockValue).prod) = 37322557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_3110213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 37322557) ^ 18661278 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37322557) ^ 12440852 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37322557) ^ 12 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_37596661 : Nat.Prime 37596661 := by
  apply lucas_primality 37596661 (2 : ZMod 37596661)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (626611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (626611, 1)] : List FactorBlock).map factorBlockValue).prod) = 37596661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_626611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37596661) ^ 18798330 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37596661) ^ 12532220 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37596661) ^ 7519332 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37596661) ^ 60 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_37748287 : Nat.Prime 37748287 := by
  apply lucas_primality 37748287 (3 : ZMod 37748287)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (29537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (29537, 1)] : List FactorBlock).map factorBlockValue).prod) = 37748287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_29537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37748287) ^ 18874143 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 12582762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 531666 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 37748287) ^ 1278 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_37763581 : Nat.Prime 37763581 := by
  apply lucas_primality 37763581 (10 : ZMod 37763581)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (31, 1), (79, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (31, 1), (79, 1), (257, 1)] : List FactorBlock).map factorBlockValue).prod) = 37763581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_79
      · exact prime_oneHundredSixtyFiveFG_257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 37763581) ^ 18881790 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 12587860 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 7552716 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 1218180 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 478020 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 37763581) ^ 146940 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_43001837 : Nat.Prime 43001837 := by
  apply lucas_primality 43001837 (2 : ZMod 43001837)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31, 1), (239, 1), (1451, 1)] : List FactorBlock).map factorBlockValue).prod) = 43001837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_239
      · exact prime_oneHundredSixtyFiveFG_1451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 43001837) ^ 21500918 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 1387156 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 179924 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 43001837) ^ 29636 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_45068029 : Nat.Prime 45068029 := by
  apply lucas_primality 45068029 (7 : ZMod 45068029)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (3755669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (3755669, 1)] : List FactorBlock).map factorBlockValue).prod) = 45068029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_3755669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 45068029) ^ 22534014 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45068029) ^ 15022676 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 45068029) ^ 12 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_57887257 : Nat.Prime 57887257 := by
  apply lucas_primality 57887257 (10 : ZMod 57887257)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (344567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (344567, 1)] : List FactorBlock).map factorBlockValue).prod) = 57887257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_344567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 57887257) ^ 28943628 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 57887257) ^ 19295752 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 57887257) ^ 8269608 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 57887257) ^ 168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_62200079 : Nat.Prime 62200079 := by
  apply lucas_primality 62200079 (7 : ZMod 62200079)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31100039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31100039, 1)] : List FactorBlock).map factorBlockValue).prod) = 62200079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_31100039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 62200079) ^ 31100039 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 62200079) ^ 2 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_68769247 : Nat.Prime 68769247 := by
  apply lucas_primality 68769247 (3 : ZMod 68769247)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (13, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (13, 1), (19, 1), (947, 1)] : List FactorBlock).map factorBlockValue).prod) = 68769247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 68769247) ^ 34384623 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 22923082 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 9824178 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 5289942 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 3619434 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 68769247) ^ 72618 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_70942363 : Nat.Prime 70942363 := by
  apply lucas_primality 70942363 (2 : ZMod 70942363)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (373, 1), (31699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (373, 1), (31699, 1)] : List FactorBlock).map factorBlockValue).prod) = 70942363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_373
      · exact prime_oneHundredSixtyFiveFG_31699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70942363) ^ 35471181 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 70942363) ^ 23647454 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 70942363) ^ 190194 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 70942363) ^ 2238 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_72522847 : Nat.Prime 72522847 := by
  apply lucas_primality 72522847 (3 : ZMod 72522847)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (366277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (366277, 1)] : List FactorBlock).map factorBlockValue).prod) = 72522847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_366277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 72522847) ^ 36261423 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72522847) ^ 24174282 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72522847) ^ 6592986 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 72522847) ^ 198 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_77414837 : Nat.Prime 77414837 := by
  apply lucas_primality 77414837 (2 : ZMod 77414837)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1873, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1873, 1), (10333, 1)] : List FactorBlock).map factorBlockValue).prod) = 77414837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_1873
      · exact prime_oneHundredSixtyFiveFG_10333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77414837) ^ 38707418 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77414837) ^ 41332 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 77414837) ^ 7492 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_80035261 : Nat.Prime 80035261 := by
  apply lucas_primality 80035261 (2 : ZMod 80035261)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (641, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (641, 1), (2081, 1)] : List FactorBlock).map factorBlockValue).prod) = 80035261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_641
      · exact prime_oneHundredSixtyFiveFG_2081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 80035261) ^ 40017630 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 26678420 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 16007052 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 124860 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 80035261) ^ 38460 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_84308839 : Nat.Prime 84308839 := by
  apply lucas_primality 84308839 (3 : ZMod 84308839)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1097, 1), (12809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1097, 1), (12809, 1)] : List FactorBlock).map factorBlockValue).prod) = 84308839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_1097
      · exact prime_oneHundredSixtyFiveFG_12809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 84308839) ^ 42154419 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 28102946 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 76854 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 84308839) ^ 6582 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_93947437 : Nat.Prime 93947437 := by
  apply lucas_primality 93947437 (5 : ZMod 93947437)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (131, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (131, 1), (1811, 1)] : List FactorBlock).map factorBlockValue).prod) = 93947437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_131
      · exact prime_oneHundredSixtyFiveFG_1811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 93947437) ^ 46973718 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 31315812 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 8540676 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 717156 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 93947437) ^ 51876 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_95533027 : Nat.Prime 95533027 := by
  apply lucas_primality 95533027 (3 : ZMod 95533027)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (541, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (541, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) = 95533027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_541
      · exact prime_oneHundredSixtyFiveFG_1549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 95533027) ^ 47766513 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95533027) ^ 31844342 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95533027) ^ 5028054 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95533027) ^ 176586 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 95533027) ^ 61674 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_95656009 : Nat.Prime 95656009 := by
  apply lucas_primality 95656009 (19 : ZMod 95656009)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (17, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (17, 1), (33493, 1)] : List FactorBlock).map factorBlockValue).prod) = 95656009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_33493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 95656009) ^ 47828004 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 31885336 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 13665144 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 5626824 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 95656009) ^ 2856 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_96720343 : Nat.Prime 96720343 := by
  apply lucas_primality 96720343 (6 : ZMod 96720343)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (16120057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (16120057, 1)] : List FactorBlock).map factorBlockValue).prod) = 96720343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_16120057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 96720343) ^ 48360171 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 96720343) ^ 32240114 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 96720343) ^ 6 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_96984187 : Nat.Prime 96984187 := by
  apply lucas_primality 96984187 (2 : ZMod 96984187)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1243387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1243387, 1)] : List FactorBlock).map factorBlockValue).prod) = 96984187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_1243387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 96984187) ^ 48492093 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 96984187) ^ 32328062 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 96984187) ^ 7460322 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 96984187) ^ 78 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_109779497 : Nat.Prime 109779497 := by
  apply lucas_primality 109779497 (3 : ZMod 109779497)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (829, 1), (16553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (829, 1), (16553, 1)] : List FactorBlock).map factorBlockValue).prod) = 109779497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_829
      · exact prime_oneHundredSixtyFiveFG_16553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 109779497) ^ 54889748 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 109779497) ^ 132424 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 109779497) ^ 6632 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_110796689 : Nat.Prime 110796689 := by
  apply lucas_primality 110796689 (3 : ZMod 110796689)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) = 110796689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_103
      · exact prime_oneHundredSixtyFiveFG_67231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110796689) ^ 55398344 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1075696 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1648 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_112452019 : Nat.Prime 112452019 := by
  apply lucas_primality 112452019 (2 : ZMod 112452019)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (911, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (911, 1), (2939, 1)] : List FactorBlock).map factorBlockValue).prod) = 112452019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_911
      · exact prime_oneHundredSixtyFiveFG_2939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 112452019) ^ 56226009 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 112452019) ^ 37484006 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 112452019) ^ 16064574 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 112452019) ^ 123438 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 112452019) ^ 38262 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_117176551 : Nat.Prime 117176551 := by
  apply lucas_primality 117176551 (3 : ZMod 117176551)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (127, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (127, 1), (6151, 1)] : List FactorBlock).map factorBlockValue).prod) = 117176551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_127
      · exact prime_oneHundredSixtyFiveFG_6151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 117176551) ^ 58588275 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 39058850 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 23435310 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 922650 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 117176551) ^ 19050 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_117717043 : Nat.Prime 117717043 := by
  apply lucas_primality 117717043 (2 : ZMod 117717043)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2711, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2711, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 117717043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2711
      · exact prime_oneHundredSixtyFiveFG_7237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 117717043) ^ 58858521 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 117717043) ^ 39239014 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 117717043) ^ 43422 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 117717043) ^ 16266 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_119623961 : Nat.Prime 119623961 := by
  apply lucas_primality 119623961 (3 : ZMod 119623961)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (37, 1), (131, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (37, 1), (131, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 119623961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_131
      · exact prime_oneHundredSixtyFiveFG_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 119623961) ^ 59811980 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 23924792 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 3233080 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 913160 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 119623961) ^ 193880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_122791657 : Nat.Prime 122791657 := by
  apply lucas_primality 122791657 (5 : ZMod 122791657)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (103, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (103, 1), (3821, 1)] : List FactorBlock).map factorBlockValue).prod) = 122791657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_103
      · exact prime_oneHundredSixtyFiveFG_3821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 122791657) ^ 61395828 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 40930552 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 9445512 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 1192152 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 122791657) ^ 32136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_128190281 : Nat.Prime 128190281 := by
  apply lucas_primality 128190281 (3 : ZMod 128190281)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (61, 1), (107, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (61, 1), (107, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 128190281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_61
      · exact prime_oneHundredSixtyFiveFG_107
      · exact prime_oneHundredSixtyFiveFG_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 128190281) ^ 64095140 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 128190281) ^ 25638056 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 128190281) ^ 2101480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 128190281) ^ 1198040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 128190281) ^ 261080 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_135346963 : Nat.Prime 135346963 := by
  apply lucas_primality 135346963 (2 : ZMod 135346963)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (37, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (37, 1), (35863, 1)] : List FactorBlock).map factorBlockValue).prod) = 135346963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_35863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 135346963) ^ 67673481 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 45115654 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 7961586 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 3658026 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 135346963) ^ 3774 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_144961759 : Nat.Prime 144961759 := by
  apply lucas_primality 144961759 (3 : ZMod 144961759)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (2684477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (2684477, 1)] : List FactorBlock).map factorBlockValue).prod) = 144961759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2684477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 144961759) ^ 72480879 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144961759) ^ 48320586 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 144961759) ^ 54 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_162317413 : Nat.Prime 162317413 := by
  apply lucas_primality 162317413 (6 : ZMod 162317413)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1502939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1502939, 1)] : List FactorBlock).map factorBlockValue).prod) = 162317413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_1502939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 162317413) ^ 81158706 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 162317413) ^ 54105804 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 162317413) ^ 108 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_169336931 : Nat.Prime 169336931 := by
  apply lucas_primality 169336931 (6 : ZMod 169336931)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (19, 1), (127321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (19, 1), (127321, 1)] : List FactorBlock).map factorBlockValue).prod) = 169336931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_127321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 169336931) ^ 84668465 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 169336931) ^ 33867386 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 169336931) ^ 24190990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 169336931) ^ 8912470 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 169336931) ^ 1330 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_180272117 : Nat.Prime 180272117 := by
  apply lucas_primality 180272117 (2 : ZMod 180272117)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (45068029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (45068029, 1)] : List FactorBlock).map factorBlockValue).prod) = 180272117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_45068029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 180272117) ^ 90136058 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 180272117) ^ 4 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_200272519 : Nat.Prime 200272519 := by
  apply lucas_primality 200272519 (15 : ZMod 200272519)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (181, 1), (61471, 1)] : List FactorBlock).map factorBlockValue).prod) = 200272519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_181
      · exact prime_oneHundredSixtyFiveFG_61471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 200272519) ^ 100136259 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 66757506 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 1106478 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 200272519) ^ 3258 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_208088557 : Nat.Prime 208088557 := by
  apply lucas_primality 208088557 (2 : ZMod 208088557)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (1333901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (1333901, 1)] : List FactorBlock).map factorBlockValue).prod) = 208088557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_1333901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 208088557) ^ 104044278 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 69362852 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 16006812 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 208088557) ^ 156 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_230845841 : Nat.Prime 230845841 := by
  apply lucas_primality 230845841 (3 : ZMod 230845841)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (31, 1), (93083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (31, 1), (93083, 1)] : List FactorBlock).map factorBlockValue).prod) = 230845841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_93083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 230845841) ^ 115422920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 46169168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 7446640 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 230845841) ^ 2480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_248048113 : Nat.Prime 248048113 := by
  apply lucas_primality 248048113 (7 : ZMod 248048113)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 248048113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 248048113) ^ 124024056 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 82682704 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19080624 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 8001552 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19344 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_274572647 : Nat.Prime 274572647 := by
  apply lucas_primality 274572647 (5 : ZMod 274572647)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (60029, 1)] : List FactorBlock).map factorBlockValue).prod) = 274572647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_2287
      · exact prime_oneHundredSixtyFiveFG_60029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 274572647) ^ 137286323 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 274572647) ^ 120058 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 274572647) ^ 4574 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_301907911 : Nat.Prime 301907911 := by
  apply lucas_primality 301907911 (15 : ZMod 301907911)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (19, 2), (61, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (19, 2), (61, 1), (457, 1)] : List FactorBlock).map factorBlockValue).prod) = 301907911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_61
      · exact prime_oneHundredSixtyFiveFG_457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 301907911) ^ 150953955 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 100635970 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 60381582 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 15889890 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 4949310 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 301907911) ^ 660630 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_316744871 : Nat.Prime 316744871 := by
  apply lucas_primality 316744871 (7 : ZMod 316744871)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 2), (187423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 2), (187423, 1)] : List FactorBlock).map factorBlockValue).prod) = 316744871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_187423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 316744871) ^ 158372435 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 316744871) ^ 63348974 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 316744871) ^ 24364990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 316744871) ^ 1690 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_320063083 : Nat.Prime 320063083 := by
  apply lucas_primality 320063083 (2 : ZMod 320063083)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (59, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (59, 1), (31177, 1)] : List FactorBlock).map factorBlockValue).prod) = 320063083 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_59
      · exact prime_oneHundredSixtyFiveFG_31177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 320063083) ^ 160031541 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 106687694 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 11036658 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 5424798 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 320063083) ^ 10266 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_330849947 : Nat.Prime 330849947 := by
  apply lucas_primality 330849947 (2 : ZMod 330849947)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (79, 1), (389, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (79, 1), (389, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) = 330849947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_79
      · exact prime_oneHundredSixtyFiveFG_389
      · exact prime_oneHundredSixtyFiveFG_769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 330849947) ^ 165424973 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 330849947) ^ 47264278 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 330849947) ^ 4187974 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 330849947) ^ 850514 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 330849947) ^ 430234 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_355354249 : Nat.Prime 355354249 := by
  apply lucas_primality 355354249 (11 : ZMod 355354249)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (811, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (811, 1), (18257, 1)] : List FactorBlock).map factorBlockValue).prod) = 355354249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_811
      · exact prime_oneHundredSixtyFiveFG_18257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 355354249) ^ 177677124 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 118451416 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 438168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 355354249) ^ 19464 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_12539
      · exact prime_oneHundredSixtyFiveFG_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_442886233 : Nat.Prime 442886233 := by
  apply lucas_primality 442886233 (7 : ZMod 442886233)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (348181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (348181, 1)] : List FactorBlock).map factorBlockValue).prod) = 442886233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_53
      · exact prime_oneHundredSixtyFiveFG_348181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 442886233) ^ 221443116 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 442886233) ^ 147628744 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 442886233) ^ 8356344 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 442886233) ^ 1272 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_467166389 : Nat.Prime 467166389 := by
  apply lucas_primality 467166389 (2 : ZMod 467166389)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (103, 1), (87223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (103, 1), (87223, 1)] : List FactorBlock).map factorBlockValue).prod) = 467166389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_103
      · exact prime_oneHundredSixtyFiveFG_87223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 467166389) ^ 233583194 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 467166389) ^ 35935876 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 467166389) ^ 4535596 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 467166389) ^ 5356 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_515976883 : Nat.Prime 515976883 := by
  apply lucas_primality 515976883 (2 : ZMod 515976883)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (101, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (101, 1), (1093, 1)] : List FactorBlock).map factorBlockValue).prod) = 515976883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_101
      · exact prime_oneHundredSixtyFiveFG_1093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 515976883) ^ 257988441 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 515976883) ^ 171992294 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 515976883) ^ 27156678 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 515976883) ^ 12584802 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 515976883) ^ 5108682 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 515976883) ^ 472074 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_540070793 : Nat.Prime 540070793 := by
  apply lucas_primality 540070793 (3 : ZMod 540070793)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1031, 1), (65479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1031, 1), (65479, 1)] : List FactorBlock).map factorBlockValue).prod) = 540070793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_1031
      · exact prime_oneHundredSixtyFiveFG_65479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 540070793) ^ 270035396 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540070793) ^ 523832 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 540070793) ^ 8248 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_541387853 : Nat.Prime 541387853 := by
  apply lucas_primality 541387853 (2 : ZMod 541387853)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (135346963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (135346963, 1)] : List FactorBlock).map factorBlockValue).prod) = 541387853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_135346963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 541387853) ^ 270693926 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 541387853) ^ 4 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_577088651 : Nat.Prime 577088651 := by
  apply lucas_primality 577088651 (2 : ZMod 577088651)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (691, 1), (16703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (691, 1), (16703, 1)] : List FactorBlock).map factorBlockValue).prod) = 577088651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_691
      · exact prime_oneHundredSixtyFiveFG_16703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 577088651) ^ 288544325 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 577088651) ^ 115417730 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 577088651) ^ 835150 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 577088651) ^ 34550 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_586365041 : Nat.Prime 586365041 := by
  apply lucas_primality 586365041 (3 : ZMod 586365041)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (557, 1), (13159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (557, 1), (13159, 1)] : List FactorBlock).map factorBlockValue).prod) = 586365041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_557
      · exact prime_oneHundredSixtyFiveFG_13159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 586365041) ^ 293182520 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 586365041) ^ 117273008 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 586365041) ^ 1052720 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 586365041) ^ 44560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_586988107 : Nat.Prime 586988107 := by
  apply lucas_primality 586988107 (5 : ZMod 586988107)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (4253537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (4253537, 1)] : List FactorBlock).map factorBlockValue).prod) = 586988107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_4253537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 586988107) ^ 293494053 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 586988107) ^ 195662702 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 586988107) ^ 25521222 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 586988107) ^ 138 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_61
      · exact prime_oneHundredSixtyFiveFG_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_674391229 : Nat.Prime 674391229 := by
  apply lucas_primality 674391229 (2 : ZMod 674391229)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (71, 1), (73, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (71, 1), (73, 1), (1549, 1)] : List FactorBlock).map factorBlockValue).prod) = 674391229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_1549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 674391229) ^ 337195614 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674391229) ^ 224797076 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674391229) ^ 96341604 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674391229) ^ 9498468 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674391229) ^ 9238236 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 674391229) ^ 435372 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_17203
      · exact prime_oneHundredSixtyFiveFG_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_773769673 : Nat.Prime 773769673 := by
  apply lucas_primality 773769673 (5 : ZMod 773769673)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (13, 1), (31, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (13, 1), (31, 1), (2963, 1)] : List FactorBlock).map factorBlockValue).prod) = 773769673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_2963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 773769673) ^ 386884836 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 773769673) ^ 257923224 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 773769673) ^ 59520744 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 773769673) ^ 24960312 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 773769673) ^ 261144 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_940799137 : Nat.Prime 940799137 := by
  apply lucas_primality 940799137 (5 : ZMod 940799137)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (19, 1), (419, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (19, 1), (419, 1), (1231, 1)] : List FactorBlock).map factorBlockValue).prod) = 940799137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_419
      · exact prime_oneHundredSixtyFiveFG_1231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 940799137) ^ 470399568 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 940799137) ^ 313599712 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 940799137) ^ 49515744 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 940799137) ^ 2245344 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 940799137) ^ 764256 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_965451497 : Nat.Prime 965451497 := by
  apply lucas_primality 965451497 (3 : ZMod 965451497)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (5247019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (5247019, 1)] : List FactorBlock).map factorBlockValue).prod) = 965451497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_5247019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 965451497) ^ 482725748 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 965451497) ^ 41976152 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 965451497) ^ 184 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1076762003 : Nat.Prime 1076762003 := by
  apply lucas_primality 1076762003 (2 : ZMod 1076762003)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (443, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (443, 1), (17117, 1)] : List FactorBlock).map factorBlockValue).prod) = 1076762003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_443
      · exact prime_oneHundredSixtyFiveFG_17117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1076762003) ^ 538381001 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 15165662 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 2430614 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1076762003) ^ 62906 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1084769671 : Nat.Prime 1084769671 := by
  apply lucas_primality 1084769671 (6 : ZMod 1084769671)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (31, 1), (443, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (31, 1), (443, 1), (2633, 1)] : List FactorBlock).map factorBlockValue).prod) = 1084769671 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_443
      · exact prime_oneHundredSixtyFiveFG_2633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1084769671) ^ 542384835 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084769671) ^ 361589890 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084769671) ^ 216953934 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084769671) ^ 34992570 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084769671) ^ 2448690 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1084769671) ^ 411990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1086248831 : Nat.Prime 1086248831 := by
  apply lucas_primality 1086248831 (13 : ZMod 1086248831)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 1), (23, 1), (277813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 1), (23, 1), (277813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1086248831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_277813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1086248831) ^ 543124415 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1086248831) ^ 217249766 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1086248831) ^ 63896990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1086248831) ^ 47228210 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 1086248831) ^ 3910 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1107895133 : Nat.Prime 1107895133 := by
  apply lucas_primality 1107895133 (2 : ZMod 1107895133)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (257, 1), (1077719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (257, 1), (1077719, 1)] : List FactorBlock).map factorBlockValue).prod) = 1107895133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_257
      · exact prime_oneHundredSixtyFiveFG_1077719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1107895133) ^ 553947566 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107895133) ^ 4310876 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1107895133) ^ 1028 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1160644117 : Nat.Prime 1160644117 := by
  apply lucas_primality 1160644117 (6 : ZMod 1160644117)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (96720343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (96720343, 1)] : List FactorBlock).map factorBlockValue).prod) = 1160644117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_96720343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1160644117) ^ 580322058 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160644117) ^ 386881372 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 1160644117) ^ 12 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1409600293 : Nat.Prime 1409600293 := by
  apply lucas_primality 1409600293 (2 : ZMod 1409600293)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (571, 1), (205721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (571, 1), (205721, 1)] : List FactorBlock).map factorBlockValue).prod) = 1409600293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_571
      · exact prime_oneHundredSixtyFiveFG_205721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1409600293) ^ 704800146 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1409600293) ^ 469866764 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1409600293) ^ 2468652 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1409600293) ^ 6852 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1658021921 : Nat.Prime 1658021921 := by
  apply lucas_primality 1658021921 (3 : ZMod 1658021921)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (10362637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (10362637, 1)] : List FactorBlock).map factorBlockValue).prod) = 1658021921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_10362637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1658021921) ^ 829010960 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1658021921) ^ 331604384 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1658021921) ^ 160 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1670696347 : Nat.Prime 1670696347 := by
  apply lucas_primality 1670696347 (5 : ZMod 1670696347)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (157, 1), (161233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (157, 1), (161233, 1)] : List FactorBlock).map factorBlockValue).prod) = 1670696347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_157
      · exact prime_oneHundredSixtyFiveFG_161233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1670696347) ^ 835348173 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1670696347) ^ 556898782 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1670696347) ^ 151881486 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1670696347) ^ 10641378 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1670696347) ^ 10362 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1706582509 : Nat.Prime 1706582509 := by
  apply lucas_primality 1706582509 (2 : ZMod 1706582509)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (139, 1), (53849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (139, 1), (53849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706582509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_139
      · exact prime_oneHundredSixtyFiveFG_53849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1706582509) ^ 853291254 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706582509) ^ 568860836 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706582509) ^ 89820132 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706582509) ^ 12277572 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1706582509) ^ 31692 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1750801123 : Nat.Prime 1750801123 := by
  apply lucas_primality 1750801123 (3 : ZMod 1750801123)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (4631749, 1)] : List FactorBlock).map factorBlockValue).prod) = 1750801123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_4631749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1750801123) ^ 875400561 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 583600374 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 250114446 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1750801123) ^ 378 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1772463233 : Nat.Prime 1772463233 := by
  apply lucas_primality 1772463233 (3 : ZMod 1772463233)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (1459, 1), (9491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (1459, 1), (9491, 1)] : List FactorBlock).map factorBlockValue).prod) = 1772463233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_1459
      · exact prime_oneHundredSixtyFiveFG_9491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1772463233) ^ 886231616 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1772463233) ^ 1214848 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1772463233) ^ 186752 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1841842939 : Nat.Prime 1841842939 := by
  apply lucas_primality 1841842939 (3 : ZMod 1841842939)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 2), (149, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 2), (149, 1), (439, 1)] : List FactorBlock).map factorBlockValue).prod) = 1841842939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_149
      · exact prime_oneHundredSixtyFiveFG_439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1841842939) ^ 920921469 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1841842939) ^ 613947646 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1841842939) ^ 141680226 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1841842939) ^ 96939102 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1841842939) ^ 12361362 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1841842939) ^ 4195542 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1861975811 : Nat.Prime 1861975811 := by
  apply lucas_primality 1861975811 (2 : ZMod 1861975811)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1861975811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_8095547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1861975811) ^ 930987905 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 372395162 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 80955470 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 230 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2520804151 : Nat.Prime 2520804151 := by
  apply lucas_primality 2520804151 (15 : ZMod 2520804151)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (5601787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (5601787, 1)] : List FactorBlock).map factorBlockValue).prod) = 2520804151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_5601787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 2520804151) ^ 1260402075 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 840268050 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 504160830 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (15 : ZMod 2520804151) ^ 450 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3288857059 : Nat.Prime 3288857059 := by
  apply lucas_primality 3288857059 (2 : ZMod 3288857059)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (79, 1), (661, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (79, 1), (661, 1), (3499, 1)] : List FactorBlock).map factorBlockValue).prod) = 3288857059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_79
      · exact prime_oneHundredSixtyFiveFG_661
      · exact prime_oneHundredSixtyFiveFG_3499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3288857059) ^ 1644428529 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3288857059) ^ 1096285686 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3288857059) ^ 41631102 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3288857059) ^ 4975578 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3288857059) ^ 939942 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4210504841 : Nat.Prime 4210504841 := by
  apply lucas_primality 4210504841 (3 : ZMod 4210504841)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (41, 1), (1229, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (41, 1), (1229, 1), (2089, 1)] : List FactorBlock).map factorBlockValue).prod) = 4210504841 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_1229
      · exact prime_oneHundredSixtyFiveFG_2089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4210504841) ^ 2105252420 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 842100968 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 102695240 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 3425960 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4210504841) ^ 2015560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4535515513 : Nat.Prime 4535515513 := by
  apply lucas_primality 4535515513 (10 : ZMod 4535515513)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (11, 1), (31, 1), (139, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (11, 1), (31, 1), (139, 1), (443, 1)] : List FactorBlock).map factorBlockValue).prod) = 4535515513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_139
      · exact prime_oneHundredSixtyFiveFG_443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 4535515513) ^ 2267757756 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4535515513) ^ 1511838504 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4535515513) ^ 412319592 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4535515513) ^ 146306952 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4535515513) ^ 32629608 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4535515513) ^ 10238184 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4690920329 : Nat.Prime 4690920329 := by
  apply lucas_primality 4690920329 (3 : ZMod 4690920329)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (586365041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (586365041, 1)] : List FactorBlock).map factorBlockValue).prod) = 4690920329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_586365041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 4690920329) ^ 2345460164 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4690920329) ^ 8 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4934049203 : Nat.Prime 4934049203 := by
  apply lucas_primality 4934049203 (2 : ZMod 4934049203)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3251, 1), (758851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3251, 1), (758851, 1)] : List FactorBlock).map factorBlockValue).prod) = 4934049203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3251
      · exact prime_oneHundredSixtyFiveFG_758851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4934049203) ^ 2467024601 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934049203) ^ 1517702 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4934049203) ^ 6502 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5113145897 : Nat.Prime 5113145897 := by
  apply lucas_primality 5113145897 (3 : ZMod 5113145897)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (37596661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (37596661, 1)] : List FactorBlock).map factorBlockValue).prod) = 5113145897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_37596661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5113145897) ^ 2556572948 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5113145897) ^ 300773288 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5113145897) ^ 136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5121009329 : Nat.Prime 5121009329 := by
  apply lucas_primality 5121009329 (3 : ZMod 5121009329)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (320063083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (320063083, 1)] : List FactorBlock).map factorBlockValue).prod) = 5121009329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_320063083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5121009329) ^ 2560504664 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5121009329) ^ 16 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5429792839 : Nat.Prime 5429792839 := by
  apply lucas_primality 5429792839 (6 : ZMod 5429792839)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (709, 1), (1276397, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429792839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_709
      · exact prime_oneHundredSixtyFiveFG_1276397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5429792839) ^ 2714896419 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 1809930946 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 7658382 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 5429792839) ^ 4254 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5638401173 : Nat.Prime 5638401173 := by
  apply lucas_primality 5638401173 (2 : ZMod 5638401173)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1409600293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1409600293, 1)] : List FactorBlock).map factorBlockValue).prod) = 5638401173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_1409600293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5638401173) ^ 2819200586 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5638401173) ^ 4 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_6852793069 : Nat.Prime 6852793069 := by
  apply lucas_primality 6852793069 (6 : ZMod 6852793069)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (17305033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (17305033, 1)] : List FactorBlock).map factorBlockValue).prod) = 6852793069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_17305033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 6852793069) ^ 3426396534 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 6852793069) ^ 2284264356 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 6852793069) ^ 622981188 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 6852793069) ^ 396 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_7137860761 : Nat.Prime 7137860761 := by
  apply lucas_primality 7137860761 (7 : ZMod 7137860761)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (449, 1), (44159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (449, 1), (44159, 1)] : List FactorBlock).map factorBlockValue).prod) = 7137860761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_449
      · exact prime_oneHundredSixtyFiveFG_44159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7137860761) ^ 3568930380 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 2379286920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 1427572152 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 15897240 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 7137860761) ^ 161640 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_7339440673 : Nat.Prime 7339440673 := by
  apply lucas_primality 7339440673 (5 : ZMod 7339440673)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (2003, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (2003, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 7339440673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2003
      · exact prime_oneHundredSixtyFiveFG_4241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7339440673) ^ 3669720336 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 2446480224 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 3664224 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 7339440673) ^ 1730592 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8256362479 : Nat.Prime 8256362479 := by
  apply lucas_primality 8256362479 (3 : ZMod 8256362479)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (15121543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (15121543, 1)] : List FactorBlock).map factorBlockValue).prod) = 8256362479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_15121543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8256362479) ^ 4128181239 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8256362479) ^ 2752120826 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8256362479) ^ 1179480354 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8256362479) ^ 635104806 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8256362479) ^ 546 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8765140303 : Nat.Prime 8765140303 := by
  apply lucas_primality 8765140303 (3 : ZMod 8765140303)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (162317413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (162317413, 1)] : List FactorBlock).map factorBlockValue).prod) = 8765140303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_162317413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8765140303) ^ 4382570151 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8765140303) ^ 2921713434 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8765140303) ^ 54 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_11270457881 : Nat.Prime 11270457881 := by
  apply lucas_primality 11270457881 (3 : ZMod 11270457881)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 2), (401, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 2), (401, 1), (5807, 1)] : List FactorBlock).map factorBlockValue).prod) = 11270457881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_401
      · exact prime_oneHundredSixtyFiveFG_5807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11270457881) ^ 5635228940 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11270457881) ^ 2254091576 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11270457881) ^ 1024587080 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11270457881) ^ 28105880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11270457881) ^ 1940840 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_11912535641 : Nat.Prime 11912535641 := by
  apply lucas_primality 11912535641 (3 : ZMod 11912535641)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (15674389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (15674389, 1)] : List FactorBlock).map factorBlockValue).prod) = 11912535641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_15674389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 11912535641) ^ 5956267820 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11912535641) ^ 2382507128 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11912535641) ^ 626975560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 11912535641) ^ 760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_15171112499 : Nat.Prime 15171112499 := by
  apply lucas_primality 15171112499 (2 : ZMod 15171112499)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (509, 1), (877, 1), (16993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (509, 1), (877, 1), (16993, 1)] : List FactorBlock).map factorBlockValue).prod) = 15171112499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_509
      · exact prime_oneHundredSixtyFiveFG_877
      · exact prime_oneHundredSixtyFiveFG_16993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 15171112499) ^ 7585556249 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15171112499) ^ 29805722 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15171112499) ^ 17298874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 15171112499) ^ 892786 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_17805412511 : Nat.Prime 17805412511 := by
  apply lucas_primality 17805412511 (19 : ZMod 17805412511)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (77414837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (77414837, 1)] : List FactorBlock).map factorBlockValue).prod) = 17805412511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_77414837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 17805412511) ^ 8902706255 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 3561082502 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 774148370 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 17805412511) ^ 230 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_18181701523 : Nat.Prime 18181701523 := by
  apply lucas_primality 18181701523 (2 : ZMod 18181701523)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (103, 1), (491, 1), (19973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (103, 1), (491, 1), (19973, 1)] : List FactorBlock).map factorBlockValue).prod) = 18181701523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_103
      · exact prime_oneHundredSixtyFiveFG_491
      · exact prime_oneHundredSixtyFiveFG_19973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18181701523) ^ 9090850761 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18181701523) ^ 6060567174 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18181701523) ^ 176521374 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18181701523) ^ 37029942 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 18181701523) ^ 910314 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_18442955497 : Nat.Prime 18442955497 := by
  apply lucas_primality 18442955497 (5 : ZMod 18442955497)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (109779497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (109779497, 1)] : List FactorBlock).map factorBlockValue).prod) = 18442955497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_109779497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 18442955497) ^ 9221477748 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18442955497) ^ 6147651832 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18442955497) ^ 2634707928 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 18442955497) ^ 168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_20969238383 : Nat.Prime 20969238383 := by
  apply lucas_primality 20969238383 (5 : ZMod 20969238383)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (80035261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (80035261, 1)] : List FactorBlock).map factorBlockValue).prod) = 20969238383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_131
      · exact prime_oneHundredSixtyFiveFG_80035261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 20969238383) ^ 10484619191 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20969238383) ^ 160070522 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 20969238383) ^ 262 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_22622892419 : Nat.Prime 22622892419 := by
  apply lucas_primality 22622892419 (2 : ZMod 22622892419)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (230845841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (230845841, 1)] : List FactorBlock).map factorBlockValue).prod) = 22622892419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_230845841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 22622892419) ^ 11311446209 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22622892419) ^ 3231841774 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 22622892419) ^ 98 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_25101738923 : Nat.Prime 25101738923 := by
  apply lucas_primality 25101738923 (2 : ZMod 25101738923)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (965451497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (965451497, 1)] : List FactorBlock).map factorBlockValue).prod) = 25101738923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_965451497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 25101738923) ^ 12550869461 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25101738923) ^ 1930902994 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25101738923) ^ 26 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_27008670877 : Nat.Prime 27008670877 := by
  apply lucas_primality 27008670877 (6 : ZMod 27008670877)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 2), (18601013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 2), (18601013, 1)] : List FactorBlock).map factorBlockValue).prod) = 27008670877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_18601013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 27008670877) ^ 13504335438 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 27008670877) ^ 9002890292 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 27008670877) ^ 2455333716 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 27008670877) ^ 1452 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_27918548017 : Nat.Prime 27918548017 := by
  apply lucas_primality 27918548017 (5 : ZMod 27918548017)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (19, 1), (30612443, 1)] : List FactorBlock).map factorBlockValue).prod) = 27918548017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_30612443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 27918548017) ^ 13959274008 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 9306182672 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 1469397264 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 27918548017) ^ 912 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_29538723241 : Nat.Prime 29538723241 := by
  apply lucas_primality 29538723241 (7 : ZMod 29538723241)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (13, 1), (31, 1), (97, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (13, 1), (31, 1), (97, 1), (2099, 1)] : List FactorBlock).map factorBlockValue).prod) = 29538723241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_97
      · exact prime_oneHundredSixtyFiveFG_2099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 29538723241) ^ 14769361620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 9846241080 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 5907744648 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 2272209480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 952862040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 304522920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 29538723241) ^ 14072760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_30352877609 : Nat.Prime 30352877609 := by
  apply lucas_primality 30352877609 (3 : ZMod 30352877609)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (41, 1), (67, 1), (97, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (41, 1), (67, 1), (97, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 30352877609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_67
      · exact prime_oneHundredSixtyFiveFG_97
      · exact prime_oneHundredSixtyFiveFG_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30352877609) ^ 15176438804 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 1046650952 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 740314088 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 453028024 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 312916264 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 30352877609) ^ 61818488 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_31697357779 : Nat.Prime 31697357779 := by
  apply lucas_primality 31697357779 (2 : ZMod 31697357779)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (586988107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (586988107, 1)] : List FactorBlock).map factorBlockValue).prod) = 31697357779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_586988107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31697357779) ^ 15848678889 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31697357779) ^ 10565785926 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31697357779) ^ 54 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_32417312623 : Nat.Prime 32417312623 := by
  apply lucas_primality 32417312623 (5 : ZMod 32417312623)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (337, 1), (463, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (337, 1), (463, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 32417312623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_337
      · exact prime_oneHundredSixtyFiveFG_463
      · exact prime_oneHundredSixtyFiveFG_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 32417312623) ^ 16208656311 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 32417312623) ^ 10805770874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 32417312623) ^ 1045719762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 32417312623) ^ 96193806 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 32417312623) ^ 70015794 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 32417312623) ^ 29021766 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_36155695577 : Nat.Prime 36155695577 := by
  apply lucas_primality 36155695577 (5 : ZMod 36155695577)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (13, 1), (4514947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (13, 1), (4514947, 1)] : List FactorBlock).map factorBlockValue).prod) = 36155695577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_4514947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36155695577) ^ 18077847788 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36155695577) ^ 5165099368 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36155695577) ^ 3286881416 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36155695577) ^ 2781207352 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36155695577) ^ 8008 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_37616242861 : Nat.Prime 37616242861 := by
  apply lucas_primality 37616242861 (2 : ZMod 37616242861)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (7, 1), (23, 1), (144223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (7, 1), (23, 1), (144223, 1)] : List FactorBlock).map factorBlockValue).prod) = 37616242861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_144223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 37616242861) ^ 18808121430 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 12538747620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 7523248572 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 5373748980 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 1635488820 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 37616242861) ^ 260820 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_45665306881 : Nat.Prime 45665306881 := by
  apply lucas_primality 45665306881 (14 : ZMod 45665306881)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (113, 1), (105239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (113, 1), (105239, 1)] : List FactorBlock).map factorBlockValue).prod) = 45665306881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_113
      · exact prime_oneHundredSixtyFiveFG_105239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 45665306881) ^ 22832653440 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 15221768960 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 9133061376 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 404117760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 45665306881) ^ 433920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_51287471069 : Nat.Prime 51287471069 := by
  apply lucas_primality 51287471069 (2 : ZMod 51287471069)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (139, 1), (4337, 1), (21269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (139, 1), (4337, 1), (21269, 1)] : List FactorBlock).map factorBlockValue).prod) = 51287471069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_139
      · exact prime_oneHundredSixtyFiveFG_4337
      · exact prime_oneHundredSixtyFiveFG_21269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 51287471069) ^ 25643735534 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51287471069) ^ 368974612 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51287471069) ^ 11825564 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 51287471069) ^ 2411372 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_58786275967 : Nat.Prime 58786275967 := by
  apply lucas_primality 58786275967 (3 : ZMod 58786275967)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (1033, 1), (37489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (1033, 1), (37489, 1)] : List FactorBlock).map factorBlockValue).prod) = 58786275967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_1033
      · exact prime_oneHundredSixtyFiveFG_37489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 58786275967) ^ 29393137983 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58786275967) ^ 19595425322 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58786275967) ^ 5344206906 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58786275967) ^ 2555925042 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58786275967) ^ 56908302 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 58786275967) ^ 1568094 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_60232527689 : Nat.Prime 60232527689 := by
  apply lucas_primality 60232527689 (3 : ZMod 60232527689)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (442886233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (442886233, 1)] : List FactorBlock).map factorBlockValue).prod) = 60232527689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_442886233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 60232527689) ^ 30116263844 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 60232527689) ^ 3543089864 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 60232527689) ^ 136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_71475213847 : Nat.Prime 71475213847 := by
  apply lucas_primality 71475213847 (3 : ZMod 71475213847)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11912535641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11912535641, 1)] : List FactorBlock).map factorBlockValue).prod) = 71475213847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11912535641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 71475213847) ^ 35737606923 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71475213847) ^ 23825071282 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 71475213847) ^ 6 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_73771821989 : Nat.Prime 73771821989 := by
  apply lucas_primality 73771821989 (2 : ZMod 73771821989)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18442955497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18442955497, 1)] : List FactorBlock).map factorBlockValue).prod) = 73771821989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_18442955497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 73771821989) ^ 36885910994 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 73771821989) ^ 4 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_74166855821 : Nat.Prime 74166855821 := by
  apply lucas_primality 74166855821 (2 : ZMod 74166855821)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (119623961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (119623961, 1)] : List FactorBlock).map factorBlockValue).prod) = 74166855821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_119623961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74166855821) ^ 37083427910 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 14833371164 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 2392479220 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 74166855821) ^ 620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_95480042941 : Nat.Prime 95480042941 := by
  apply lucas_primality 95480042941 (6 : ZMod 95480042941)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (137, 1), (1049, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (137, 1), (1049, 1), (3691, 1)] : List FactorBlock).map factorBlockValue).prod) = 95480042941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_137
      · exact prime_oneHundredSixtyFiveFG_1049
      · exact prime_oneHundredSixtyFiveFG_3691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 95480042941) ^ 47740021470 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 95480042941) ^ 31826680980 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 95480042941) ^ 19096008588 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 95480042941) ^ 696934620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 95480042941) ^ 91020060 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 95480042941) ^ 25868340 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_106051902181 : Nat.Prime 106051902181 := by
  apply lucas_primality 106051902181 (2 : ZMod 106051902181)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (691, 1), (365419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (691, 1), (365419, 1)] : List FactorBlock).map factorBlockValue).prod) = 106051902181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_691
      · exact prime_oneHundredSixtyFiveFG_365419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 106051902181) ^ 53025951090 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106051902181) ^ 35350634060 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106051902181) ^ 21210380436 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106051902181) ^ 15150271740 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106051902181) ^ 153475980 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 106051902181) ^ 290220 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_120055286693 : Nat.Prime 120055286693 := by
  apply lucas_primality 120055286693 (2 : ZMod 120055286693)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) = 120055286693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_248048113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120055286693) ^ 60027643346 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 10914116972 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 484 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_129669250493 : Nat.Prime 129669250493 := by
  apply lucas_primality 129669250493 (2 : ZMod 129669250493)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (32417312623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (32417312623, 1)] : List FactorBlock).map factorBlockValue).prod) = 129669250493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_32417312623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 129669250493) ^ 64834625246 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 129669250493) ^ 4 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_853
      · exact prime_oneHundredSixtyFiveFG_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_147543643979 : Nat.Prime 147543643979 := by
  apply lucas_primality 147543643979 (2 : ZMod 147543643979)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73771821989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73771821989, 1)] : List FactorBlock).map factorBlockValue).prod) = 147543643979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_73771821989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 147543643979) ^ 73771821989 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 147543643979) ^ 2 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_154518491651 : Nat.Prime 154518491651 := by
  apply lucas_primality 154518491651 (2 : ZMod 154518491651)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (37, 1), (2880121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (37, 1), (2880121, 1)] : List FactorBlock).map factorBlockValue).prod) = 154518491651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_2880121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 154518491651) ^ 77259245825 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 30903698330 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 5328223850 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 4176175450 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 154518491651) ^ 53650 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_156583512721 : Nat.Prime 156583512721 := by
  apply lucas_primality 156583512721 (7 : ZMod 156583512721)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (5, 1), (43, 1), (1685869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (5, 1), (43, 1), (1685869, 1)] : List FactorBlock).map factorBlockValue).prod) = 156583512721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_43
      · exact prime_oneHundredSixtyFiveFG_1685869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 156583512721) ^ 78291756360 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 156583512721) ^ 52194504240 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 156583512721) ^ 31316702544 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 156583512721) ^ 3641477040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 156583512721) ^ 92880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_222133410637 : Nat.Prime 222133410637 := by
  apply lucas_primality 222133410637 (5 : ZMod 222133410637)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 222133410637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_373
      · exact prime_oneHundredSixtyFiveFG_3449
      · exact prime_oneHundredSixtyFiveFG_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222133410637) ^ 111066705318 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 74044470212 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 595531932 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 64405164 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 15437724 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_338304070381 : Nat.Prime 338304070381 := by
  apply lucas_primality 338304070381 (2 : ZMod 338304070381)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5638401173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5638401173, 1)] : List FactorBlock).map factorBlockValue).prod) = 338304070381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_5638401173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 338304070381) ^ 169152035190 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 338304070381) ^ 112768023460 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 338304070381) ^ 67660814076 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 338304070381) ^ 60 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_347200840979 : Nat.Prime 347200840979 := by
  apply lucas_primality 347200840979 (2 : ZMod 347200840979)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2791, 1), (62200079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2791, 1), (62200079, 1)] : List FactorBlock).map factorBlockValue).prod) = 347200840979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_2791
      · exact prime_oneHundredSixtyFiveFG_62200079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 347200840979) ^ 173600420489 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 347200840979) ^ 124400158 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 347200840979) ^ 5582 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_476907466417 : Nat.Prime 476907466417 := by
  apply lucas_primality 476907466417 (10 : ZMod 476907466417)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (43, 1), (73, 1), (3165203, 1)] : List FactorBlock).map factorBlockValue).prod) = 476907466417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_43
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_3165203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 476907466417) ^ 238453733208 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 158969155472 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 11090871312 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 6532978992 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 476907466417) ^ 150672 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_526815301981 : Nat.Prime 526815301981 := by
  apply lucas_primality 526815301981 (2 : ZMod 526815301981)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (1321, 1), (604243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (1321, 1), (604243, 1)] : List FactorBlock).map factorBlockValue).prod) = 526815301981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_1321
      · exact prime_oneHundredSixtyFiveFG_604243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 526815301981) ^ 263407650990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 175605100660 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 105363060396 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 47892300180 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 398800380 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 526815301981) ^ 871860 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_583527732737 : Nat.Prime 583527732737 := by
  apply lucas_primality 583527732737 (3 : ZMod 583527732737)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (13, 1), (2803, 1), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (13, 1), (2803, 1), (31277, 1)] : List FactorBlock).map factorBlockValue).prod) = 583527732737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_2803
      · exact prime_oneHundredSixtyFiveFG_31277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 583527732737) ^ 291763866368 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 44886748672 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 208179712 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 583527732737) ^ 18656768 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_667616203883 : Nat.Prime 667616203883 := by
  apply lucas_primality 667616203883 (2 : ZMod 667616203883)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (239, 1), (37748287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (239, 1), (37748287, 1)] : List FactorBlock).map factorBlockValue).prod) = 667616203883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_239
      · exact prime_oneHundredSixtyFiveFG_37748287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 667616203883) ^ 333808101941 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 18043681186 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 2793373238 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 667616203883) ^ 17686 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_694401681959 : Nat.Prime 694401681959 := by
  apply lucas_primality 694401681959 (13 : ZMod 694401681959)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (347200840979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (347200840979, 1)] : List FactorBlock).map factorBlockValue).prod) = 694401681959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_347200840979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (13 : ZMod 694401681959) ^ 347200840979 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 694401681959) ^ 2 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_927457690639 : Nat.Prime 927457690639 := by
  apply lucas_primality 927457690639 (3 : ZMod 927457690639)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (3288857059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (3288857059, 1)] : List FactorBlock).map factorBlockValue).prod) = 927457690639 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_3288857059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 927457690639) ^ 463728845319 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 927457690639) ^ 309152563546 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 927457690639) ^ 19733142354 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 927457690639) ^ 282 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1060519021811 : Nat.Prime 1060519021811 := by
  apply lucas_primality 1060519021811 (2 : ZMod 1060519021811)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (106051902181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (106051902181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1060519021811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_106051902181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1060519021811) ^ 530259510905 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1060519021811) ^ 212103804362 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1060519021811) ^ 10 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1295508299753 : Nat.Prime 1295508299753 := by
  apply lucas_primality 1295508299753 (3 : ZMod 1295508299753)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (43759, 1), (3700691, 1)] : List FactorBlock).map factorBlockValue).prod) = 1295508299753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_43759
      · exact prime_oneHundredSixtyFiveFG_3700691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1295508299753) ^ 647754149876 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 29605528 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1295508299753) ^ 350072 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1477220469691 : Nat.Prime 1477220469691 := by
  apply lucas_primality 1477220469691 (7 : ZMod 1477220469691)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (1171, 1), (6007159, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (1171, 1), (6007159, 1)] : List FactorBlock).map factorBlockValue).prod) = 1477220469691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_1171
      · exact prime_oneHundredSixtyFiveFG_6007159
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1477220469691) ^ 738610234845 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 492406823230 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 295444093938 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 211031495670 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 1261503390 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1477220469691) ^ 245910 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2110920943181 : Nat.Prime 2110920943181 := by
  apply lucas_primality 2110920943181 (2 : ZMod 2110920943181)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (40039, 1), (376583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (40039, 1), (376583, 1)] : List FactorBlock).map factorBlockValue).prod) = 2110920943181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_40039
      · exact prime_oneHundredSixtyFiveFG_376583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2110920943181) ^ 1055460471590 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2110920943181) ^ 422184188636 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2110920943181) ^ 301560134740 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2110920943181) ^ 52721620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2110920943181) ^ 5605460 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2340099468701 : Nat.Prime 2340099468701 := by
  apply lucas_primality 2340099468701 (2 : ZMod 2340099468701)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (7, 1), (397, 1), (8420653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (7, 1), (397, 1), (8420653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2340099468701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_397
      · exact prime_oneHundredSixtyFiveFG_8420653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2340099468701) ^ 1170049734350 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340099468701) ^ 468019893740 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340099468701) ^ 334299924100 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340099468701) ^ 5894457100 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 2340099468701) ^ 277900 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2786044081081 : Nat.Prime 2786044081081 := by
  apply lucas_primality 2786044081081 (11 : ZMod 2786044081081)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13, 1), (47, 2), (59, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13, 1), (47, 2), (59, 1), (71, 1), (193, 1)] : List FactorBlock).map factorBlockValue).prod) = 2786044081081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_59
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 2786044081081) ^ 1393022040540 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 928681360360 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 557208816216 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 214311083160 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 59277533640 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 47221086120 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 39240057480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 2786044081081) ^ 14435461560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3343093065173 : Nat.Prime 3343093065173 := by
  apply lucas_primality 3343093065173 (2 : ZMod 3343093065173)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (12893, 1), (487397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (12893, 1), (487397, 1)] : List FactorBlock).map factorBlockValue).prod) = 3343093065173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_12893
      · exact prime_oneHundredSixtyFiveFG_487397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3343093065173) ^ 1671546532586 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343093065173) ^ 477584723596 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343093065173) ^ 175952266588 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343093065173) ^ 259295204 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3343093065173) ^ 6859076 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4362013817011 : Nat.Prime 4362013817011 := by
  apply lucas_primality 4362013817011 (2 : ZMod 4362013817011)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (431, 1), (112452019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (431, 1), (112452019, 1)] : List FactorBlock).map factorBlockValue).prod) = 4362013817011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_431
      · exact prime_oneHundredSixtyFiveFG_112452019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4362013817011) ^ 2181006908505 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362013817011) ^ 1454004605670 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362013817011) ^ 872402763402 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362013817011) ^ 10120681710 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362013817011) ^ 38790 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4383869460577 : Nat.Prime 4383869460577 := by
  apply lucas_primality 4383869460577 (10 : ZMod 4383869460577)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (45665306881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (45665306881, 1)] : List FactorBlock).map factorBlockValue).prod) = 4383869460577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_45665306881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 4383869460577) ^ 2191934730288 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4383869460577) ^ 1461289820192 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 4383869460577) ^ 96 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4542054392287 : Nat.Prime 4542054392287 := by
  apply lucas_primality 4542054392287 (3 : ZMod 4542054392287)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (73, 1), (84308839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (73, 1), (84308839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4542054392287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_84308839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4542054392287) ^ 2271027196143 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 1514018130762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 110781814446 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 62219923182 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 4542054392287) ^ 53874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_7020381470099 : Nat.Prime 7020381470099 := by
  apply lucas_primality 7020381470099 (2 : ZMod 7020381470099)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6803, 1), (515976883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6803, 1), (515976883, 1)] : List FactorBlock).map factorBlockValue).prod) = 7020381470099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_6803
      · exact prime_oneHundredSixtyFiveFG_515976883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 7020381470099) ^ 3510190735049 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020381470099) ^ 1031953766 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 7020381470099) ^ 13606 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_7214541480163 : Nat.Prime 7214541480163 := by
  apply lucas_primality 7214541480163 (3 : ZMod 7214541480163)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (53, 1), (2520804151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (53, 1), (2520804151, 1)] : List FactorBlock).map factorBlockValue).prod) = 7214541480163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_53
      · exact prime_oneHundredSixtyFiveFG_2520804151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7214541480163) ^ 3607270740081 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 2404847160054 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 136123424154 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7214541480163) ^ 2862 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8503336257881 : Nat.Prime 8503336257881 := by
  apply lucas_primality 8503336257881 (3 : ZMod 8503336257881)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (47, 1), (877, 1), (1901, 1), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (47, 1), (877, 1), (1901, 1), (2713, 1)] : List FactorBlock).map factorBlockValue).prod) = 8503336257881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_877
      · exact prime_oneHundredSixtyFiveFG_1901
      · exact prime_oneHundredSixtyFiveFG_2713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8503336257881) ^ 4251668128940 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 1700667251576 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 180922048040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 9695936440 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 4473085880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8503336257881) ^ 3134292760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8638877807737 : Nat.Prime 8638877807737 := by
  apply lucas_primality 8638877807737 (13 : ZMod 8638877807737)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (17, 1), (109, 1), (283, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (17, 1), (109, 1), (283, 1), (62401, 1)] : List FactorBlock).map factorBlockValue).prod) = 8638877807737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_109
      · exact prime_oneHundredSixtyFiveFG_283
      · exact prime_oneHundredSixtyFiveFG_62401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 8638877807737) ^ 4319438903868 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 2879625935912 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 785352527976 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 508169282808 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 79255759704 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 30526069992 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 8638877807737) ^ 138441336 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_10657483763819 : Nat.Prime 10657483763819 := by
  apply lucas_primality 10657483763819 (2 : ZMod 10657483763819)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (347, 1), (1427, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (347, 1), (1427, 1), (98729, 1)] : List FactorBlock).map factorBlockValue).prod) = 10657483763819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_109
      · exact prime_oneHundredSixtyFiveFG_347
      · exact prime_oneHundredSixtyFiveFG_1427
      · exact prime_oneHundredSixtyFiveFG_98729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10657483763819) ^ 5328741881909 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 97775080402 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 30713209694 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 7468453934 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10657483763819) ^ 107946842 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_13908918562933 : Nat.Prime 13908918562933 := by
  apply lucas_primality 13908918562933 (2 : ZMod 13908918562933)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (20023, 1), (57887257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (20023, 1), (57887257, 1)] : List FactorBlock).map factorBlockValue).prod) = 13908918562933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_20023
      · exact prime_oneHundredSixtyFiveFG_57887257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13908918562933) ^ 6954459281466 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13908918562933) ^ 4636306187644 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13908918562933) ^ 694647084 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 13908918562933) ^ 240276 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_19104580532281 : Nat.Prime 19104580532281 := by
  apply lucas_primality 19104580532281 (19 : ZMod 19104580532281)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (17, 1), (79, 1), (7993, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (17, 1), (79, 1), (7993, 1), (14831, 1)] : List FactorBlock).map factorBlockValue).prod) = 19104580532281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_79
      · exact prime_oneHundredSixtyFiveFG_7993
      · exact prime_oneHundredSixtyFiveFG_14831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 19104580532281) ^ 9552290266140 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 6368193510760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 3820916106456 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 1123798854840 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 241830133320 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 2390163960 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (19 : ZMod 19104580532281) ^ 1288151880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_19456411085651 : Nat.Prime 19456411085651 := by
  apply lucas_primality 19456411085651 (2 : ZMod 19456411085651)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (11, 1), (347, 1), (1171, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (11, 1), (347, 1), (1171, 1), (12437, 1)] : List FactorBlock).map factorBlockValue).prod) = 19456411085651 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_347
      · exact prime_oneHundredSixtyFiveFG_1171
      · exact prime_oneHundredSixtyFiveFG_12437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19456411085651) ^ 9728205542825 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 3891282217130 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 2779487297950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 1768764644150 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 56070348950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 16615210150 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 19456411085651) ^ 1564397450 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_21195094540883 : Nat.Prime 21195094540883 := by
  apply lucas_primality 21195094540883 (2 : ZMod 21195094540883)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (2111, 1), (68769247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (2111, 1), (68769247, 1)] : List FactorBlock).map factorBlockValue).prod) = 21195094540883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_2111
      · exact prime_oneHundredSixtyFiveFG_68769247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 21195094540883) ^ 10597547270441 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 290343760834 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 10040310062 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 21195094540883) ^ 308206 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_47061672383657 : Nat.Prime 47061672383657 := by
  apply lucas_primality 47061672383657 (3 : ZMod 47061672383657)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) = 47061672383657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_120055286693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47061672383657) ^ 23530836191828 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 6723096054808 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 392 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_48551312878337 : Nat.Prime 48551312878337 := by
  apply lucas_primality 48551312878337 (3 : ZMod 48551312878337)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (107, 1), (1772463233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (107, 1), (1772463233, 1)] : List FactorBlock).map factorBlockValue).prod) = 48551312878337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_107
      · exact prime_oneHundredSixtyFiveFG_1772463233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 48551312878337) ^ 24275656439168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 48551312878337) ^ 453750587648 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 48551312878337) ^ 27392 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_59736561858227 : Nat.Prime 59736561858227 := by
  apply lucas_primality 59736561858227 (2 : ZMod 59736561858227)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1471, 1), (1951, 1), (946123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1471, 1), (1951, 1), (946123, 1)] : List FactorBlock).map factorBlockValue).prod) = 59736561858227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_1471
      · exact prime_oneHundredSixtyFiveFG_1951
      · exact prime_oneHundredSixtyFiveFG_946123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59736561858227) ^ 29868280929113 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59736561858227) ^ 5430596532566 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59736561858227) ^ 40609491406 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59736561858227) ^ 30618432526 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 59736561858227) ^ 63138262 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_66139999399751 : Nat.Prime 66139999399751 := by
  apply lucas_primality 66139999399751 (7 : ZMod 66139999399751)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (1321, 1), (200272519, 1)] : List FactorBlock).map factorBlockValue).prod) = 66139999399751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_1321
      · exact prime_oneHundredSixtyFiveFG_200272519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 66139999399751) ^ 33069999699875 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 13227999879950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 50068129750 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 66139999399751) ^ 330250 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_173
      · exact prime_oneHundredSixtyFiveFG_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_119246988861851 : Nat.Prime 119246988861851 := by
  apply lucas_primality 119246988861851 (2 : ZMod 119246988861851)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (227, 1), (80077, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (227, 1), (80077, 1), (131203, 1)] : List FactorBlock).map factorBlockValue).prod) = 119246988861851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_227
      · exact prime_oneHundredSixtyFiveFG_80077
      · exact prime_oneHundredSixtyFiveFG_131203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 119246988861851) ^ 59623494430925 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 119246988861851) ^ 23849397772370 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 119246988861851) ^ 525317131550 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 119246988861851) ^ 1489154050 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 119246988861851) ^ 908873950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_179403328798297 : Nat.Prime 179403328798297 := by
  apply lucas_primality 179403328798297 (5 : ZMod 179403328798297)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (73, 1), (42589, 1), (2404357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (73, 1), (42589, 1), (2404357, 1)] : List FactorBlock).map factorBlockValue).prod) = 179403328798297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_42589
      · exact prime_oneHundredSixtyFiveFG_2404357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 179403328798297) ^ 89701664399148 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 59801109599432 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 2457579846552 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 4212433464 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 179403328798297) ^ 74615928 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_201243445356743 : Nat.Prime 201243445356743 := by
  apply lucas_primality 201243445356743 (5 : ZMod 201243445356743)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (191, 1), (526815301981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (191, 1), (526815301981, 1)] : List FactorBlock).map factorBlockValue).prod) = 201243445356743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_191
      · exact prime_oneHundredSixtyFiveFG_526815301981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 201243445356743) ^ 100621722678371 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 201243445356743) ^ 1053630603962 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 201243445356743) ^ 382 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_221173209466147 : Nat.Prime 221173209466147 := by
  apply lucas_primality 221173209466147 (2 : ZMod 221173209466147)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2131, 1), (274572647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2131, 1), (274572647, 1)] : List FactorBlock).map factorBlockValue).prod) = 221173209466147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_2131
      · exact prime_oneHundredSixtyFiveFG_274572647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 221173209466147) ^ 110586604733073 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 73724403155382 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 31596172780878 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 103788460566 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 221173209466147) ^ 805518 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_273308408322643 : Nat.Prime 273308408322643 := by
  apply lucas_primality 273308408322643 (3 : ZMod 273308408322643)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) = 273308408322643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_1109
      · exact prime_oneHundredSixtyFiveFG_5273
      · exact prime_oneHundredSixtyFiveFG_33721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 273308408322643) ^ 136654204161321 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 91102802774214 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 39044058331806 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 24846218938422 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 246445814538 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 51831672354 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 8104991202 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_335707867311353 : Nat.Prime 335707867311353 := by
  apply lucas_primality 335707867311353 (3 : ZMod 335707867311353)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5879, 1), (7137860761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5879, 1), (7137860761, 1)] : List FactorBlock).map factorBlockValue).prod) = 335707867311353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5879
      · exact prime_oneHundredSixtyFiveFG_7137860761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 335707867311353) ^ 167853933655676 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 335707867311353) ^ 57102886088 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 335707867311353) ^ 47032 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_402486890713487 : Nat.Prime 402486890713487 := by
  apply lucas_primality 402486890713487 (5 : ZMod 402486890713487)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (201243445356743, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (201243445356743, 1)] : List FactorBlock).map factorBlockValue).prod) = 402486890713487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_201243445356743
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 402486890713487) ^ 201243445356743 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 402486890713487) ^ 2 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_407397001991621 : Nat.Prime 407397001991621 := by
  apply lucas_primality 407397001991621 (2 : ZMod 407397001991621)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37717, 1), (540070793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37717, 1), (540070793, 1)] : List FactorBlock).map factorBlockValue).prod) = 407397001991621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_37717
      · exact prime_oneHundredSixtyFiveFG_540070793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 407397001991621) ^ 203698500995810 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 407397001991621) ^ 81479400398324 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 407397001991621) ^ 10801415860 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 407397001991621) ^ 754340 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_434515305643609 : Nat.Prime 434515305643609 := by
  apply lucas_primality 434515305643609 (13 : ZMod 434515305643609)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (161977, 1), (15967703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (161977, 1), (15967703, 1)] : List FactorBlock).map factorBlockValue).prod) = 434515305643609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_161977
      · exact prime_oneHundredSixtyFiveFG_15967703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 434515305643609) ^ 217257652821804 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 434515305643609) ^ 144838435214536 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 434515305643609) ^ 62073615091944 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 434515305643609) ^ 2682574104 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 434515305643609) ^ 27212136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_439099334161333 : Nat.Prime 439099334161333 := by
  apply lucas_primality 439099334161333 (2 : ZMod 439099334161333)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (239, 1), (35603, 1), (330791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (239, 1), (35603, 1), (330791, 1)] : List FactorBlock).map factorBlockValue).prod) = 439099334161333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_239
      · exact prime_oneHundredSixtyFiveFG_35603
      · exact prime_oneHundredSixtyFiveFG_330791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 439099334161333) ^ 219549667080666 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 146366444720444 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 33776871858564 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 1837235707788 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 12333211644 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 439099334161333) ^ 1327422252 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_502177283554481 : Nat.Prime 502177283554481 := by
  apply lucas_primality 502177283554481 (3 : ZMod 502177283554481)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (18973, 1), (330849947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (18973, 1), (330849947, 1)] : List FactorBlock).map factorBlockValue).prod) = 502177283554481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_18973
      · exact prime_oneHundredSixtyFiveFG_330849947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 502177283554481) ^ 251088641777240 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 502177283554481) ^ 100435456710896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 502177283554481) ^ 26467995760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 502177283554481) ^ 1517840 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_591592401373367 : Nat.Prime 591592401373367 := by
  apply lucas_primality 591592401373367 (5 : ZMod 591592401373367)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (7214541480163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (7214541480163, 1)] : List FactorBlock).map factorBlockValue).prod) = 591592401373367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_7214541480163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 591592401373367) ^ 295796200686683 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 591592401373367) ^ 14429082960326 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 591592401373367) ^ 82 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_626551724582803 : Nat.Prime 626551724582803 := by
  apply lucas_primality 626551724582803 (3 : ZMod 626551724582803)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (487, 1), (71475213847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (487, 1), (71475213847, 1)] : List FactorBlock).map factorBlockValue).prod) = 626551724582803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_487
      · exact prime_oneHundredSixtyFiveFG_71475213847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 626551724582803) ^ 313275862291401 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 626551724582803) ^ 208850574860934 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 626551724582803) ^ 1286553849246 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 626551724582803) ^ 8766 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_643273943197409 : Nat.Prime 643273943197409 := by
  apply lucas_primality 643273943197409 (3 : ZMod 643273943197409)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (1129, 1), (17805412511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (1129, 1), (17805412511, 1)] : List FactorBlock).map factorBlockValue).prod) = 643273943197409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_1129
      · exact prime_oneHundredSixtyFiveFG_17805412511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 643273943197409) ^ 321636971598704 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 643273943197409) ^ 569773200352 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 643273943197409) ^ 36128 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_723857833738631 : Nat.Prime 723857833738631 := by
  apply lucas_primality 723857833738631 (7 : ZMod 723857833738631)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (113, 1), (153457, 1), (4174343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (113, 1), (153457, 1), (4174343, 1)] : List FactorBlock).map factorBlockValue).prod) = 723857833738631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_113
      · exact prime_oneHundredSixtyFiveFG_153457
      · exact prime_oneHundredSixtyFiveFG_4174343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 723857833738631) ^ 361928916869315 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 144771566747726 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 6405821537510 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 4717007590 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 723857833738631) ^ 173406410 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_802151169023389 : Nat.Prime 802151169023389 := by
  apply lucas_primality 802151169023389 (6 : ZMod 802151169023389)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2663, 1), (25101738923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2663, 1), (25101738923, 1)] : List FactorBlock).map factorBlockValue).prod) = 802151169023389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2663
      · exact prime_oneHundredSixtyFiveFG_25101738923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 802151169023389) ^ 401075584511694 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 802151169023389) ^ 267383723007796 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 802151169023389) ^ 301220867076 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 802151169023389) ^ 31956 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1084850985537467 : Nat.Prime 1084850985537467 := by
  apply lucas_primality 1084850985537467 (2 : ZMod 1084850985537467)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37, 1), (4483, 1), (467166389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37, 1), (4483, 1), (467166389, 1)] : List FactorBlock).map factorBlockValue).prod) = 1084850985537467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_4483
      · exact prime_oneHundredSixtyFiveFG_467166389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1084850985537467) ^ 542425492768733 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084850985537467) ^ 154978712219638 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084850985537467) ^ 29320296906418 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084850985537467) ^ 241992189502 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1084850985537467) ^ 2322194 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1308639295634981 : Nat.Prime 1308639295634981 := by
  apply lucas_primality 1308639295634981 (3 : ZMod 1308639295634981)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5171, 1), (31699, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5171, 1), (31699, 1), (399181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1308639295634981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_5171
      · exact prime_oneHundredSixtyFiveFG_31699
      · exact prime_oneHundredSixtyFiveFG_399181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1308639295634981) ^ 654319647817490 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 261727859126996 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 253072770380 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 41283299020 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1308639295634981) ^ 3278310580 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1328290958879329 : Nat.Prime 1328290958879329 := by
  apply lucas_primality 1328290958879329 (17 : ZMod 1328290958879329)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (433439, 1), (31922287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (433439, 1), (31922287, 1)] : List FactorBlock).map factorBlockValue).prod) = 1328290958879329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_433439
      · exact prime_oneHundredSixtyFiveFG_31922287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 1328290958879329) ^ 664145479439664 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1328290958879329) ^ 442763652959776 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1328290958879329) ^ 3064539552 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (17 : ZMod 1328290958879329) ^ 41610144 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1368724432009199 : Nat.Prime 1368724432009199 := by
  apply lucas_primality 1368724432009199 (11 : ZMod 1368724432009199)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (17, 1), (71, 1), (97, 1), (4259, 1), (124769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (17, 1), (71, 1), (97, 1), (4259, 1), (124769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1368724432009199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_97
      · exact prime_oneHundredSixtyFiveFG_4259
      · exact prime_oneHundredSixtyFiveFG_124769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1368724432009199) ^ 684362216004599 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 124429493819018 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 80513201882894 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 19277808901538 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 14110561154734 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 321372254522 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 1368724432009199) ^ 10970068142 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2444382011949727 : Nat.Prime 2444382011949727 := by
  apply lucas_primality 2444382011949727 (3 : ZMod 2444382011949727)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (407397001991621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (407397001991621, 1)] : List FactorBlock).map factorBlockValue).prod) = 2444382011949727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_407397001991621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2444382011949727) ^ 1222191005974863 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2444382011949727) ^ 814794003983242 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2444382011949727) ^ 6 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3432433098085627 : Nat.Prime 3432433098085627 := by
  apply lucas_primality 3432433098085627 (3 : ZMod 3432433098085627)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (89, 1), (338304070381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (89, 1), (338304070381, 1)] : List FactorBlock).map factorBlockValue).prod) = 3432433098085627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_89
      · exact prime_oneHundredSixtyFiveFG_338304070381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3432433098085627) ^ 1716216549042813 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3432433098085627) ^ 1144144366028542 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3432433098085627) ^ 180654373583454 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3432433098085627) ^ 38566664023434 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3432433098085627) ^ 10146 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3860746233443951 : Nat.Prime 3860746233443951 := by
  apply lucas_primality 3860746233443951 (11 : ZMod 3860746233443951)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (17, 1), (4542054392287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (17, 1), (4542054392287, 1)] : List FactorBlock).map factorBlockValue).prod) = 3860746233443951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_4542054392287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3860746233443951) ^ 1930373116721975 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 772149246688790 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 227102719614350 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 3860746233443951) ^ 850 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3991695145719031 : Nat.Prime 3991695145719031 := by
  apply lucas_primality 3991695145719031 (6 : ZMod 3991695145719031)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (89, 1), (101, 1), (4934049203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (89, 1), (101, 1), (4934049203, 1)] : List FactorBlock).map factorBlockValue).prod) = 3991695145719031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_89
      · exact prime_oneHundredSixtyFiveFG_101
      · exact prime_oneHundredSixtyFiveFG_4934049203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3991695145719031) ^ 1995847572859515 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3991695145719031) ^ 1330565048573010 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3991695145719031) ^ 798339029143806 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3991695145719031) ^ 44850507255270 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3991695145719031) ^ 39521734116030 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 3991695145719031) ^ 809010 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5790862669909049 : Nat.Prime 5790862669909049 := by
  apply lucas_primality 5790862669909049 (3 : ZMod 5790862669909049)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (723857833738631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (723857833738631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5790862669909049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_723857833738631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 5790862669909049) ^ 2895431334954524 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 5790862669909049) ^ 8 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_6426628307172589 : Nat.Prime 6426628307172589 := by
  apply lucas_primality 6426628307172589 (2 : ZMod 6426628307172589)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5791, 1), (11243, 1), (8225573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5791, 1), (11243, 1), (8225573, 1)] : List FactorBlock).map factorBlockValue).prod) = 6426628307172589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5791
      · exact prime_oneHundredSixtyFiveFG_11243
      · exact prime_oneHundredSixtyFiveFG_8225573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6426628307172589) ^ 3213314153586294 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6426628307172589) ^ 2142209435724196 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6426628307172589) ^ 1109761406868 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6426628307172589) ^ 571611518916 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6426628307172589) ^ 781298556 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_6982819718723939 : Nat.Prime 6982819718723939 := by
  apply lucas_primality 6982819718723939 (2 : ZMod 6982819718723939)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (79, 1), (1583, 1), (27918548017, 1)] : List FactorBlock).map factorBlockValue).prod) = 6982819718723939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_79
      · exact prime_oneHundredSixtyFiveFG_1583
      · exact prime_oneHundredSixtyFiveFG_27918548017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6982819718723939) ^ 3491409859361969 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 88390123021822 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 4411130586686 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6982819718723939) ^ 250114 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_7955553520153241 : Nat.Prime 7955553520153241 := by
  apply lucas_primality 7955553520153241 (3 : ZMod 7955553520153241)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (19, 1), (72211, 1), (144961759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (19, 1), (72211, 1), (144961759, 1)] : List FactorBlock).map factorBlockValue).prod) = 7955553520153241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_72211
      · exact prime_oneHundredSixtyFiveFG_144961759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7955553520153241) ^ 3977776760076620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 1591110704030648 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 418713343165960 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 110170936840 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 7955553520153241) ^ 54880360 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_9659685377123689 : Nat.Prime 9659685377123689 := by
  apply lucas_primality 9659685377123689 (7 : ZMod 9659685377123689)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (402486890713487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (402486890713487, 1)] : List FactorBlock).map factorBlockValue).prod) = 9659685377123689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_402486890713487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 9659685377123689) ^ 4829842688561844 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 9659685377123689) ^ 3219895125707896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 9659685377123689) ^ 24 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_14541284492348387 : Nat.Prime 14541284492348387 := by
  apply lucas_primality 14541284492348387 (2 : ZMod 14541284492348387)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (787, 1), (156583512721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (787, 1), (156583512721, 1)] : List FactorBlock).map factorBlockValue).prod) = 14541284492348387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_59
      · exact prime_oneHundredSixtyFiveFG_787
      · exact prime_oneHundredSixtyFiveFG_156583512721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14541284492348387) ^ 7270642246174193 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14541284492348387) ^ 246462449022854 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14541284492348387) ^ 18476854501078 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 14541284492348387) ^ 92866 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_15889925454288383 : Nat.Prime 15889925454288383 := by
  apply lucas_primality 15889925454288383 (5 : ZMod 15889925454288383)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (59736561858227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (59736561858227, 1)] : List FactorBlock).map factorBlockValue).prod) = 15889925454288383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_59736561858227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 15889925454288383) ^ 7944962727144191 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15889925454288383) ^ 2269989350612626 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15889925454288383) ^ 836311866015178 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 15889925454288383) ^ 266 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_20033494128790969 : Nat.Prime 20033494128790969 := by
  apply lucas_primality 20033494128790969 (11 : ZMod 20033494128790969)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (119246988861851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (119246988861851, 1)] : List FactorBlock).map factorBlockValue).prod) = 20033494128790969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_119246988861851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 20033494128790969) ^ 10016747064395484 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 20033494128790969) ^ 6677831376263656 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 20033494128790969) ^ 2861927732684424 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 20033494128790969) ^ 168 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_25679504286205909 : Nat.Prime 25679504286205909 := by
  apply lucas_primality 25679504286205909 (2 : ZMod 25679504286205909)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (167009, 1), (674391229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (167009, 1), (674391229, 1)] : List FactorBlock).map factorBlockValue).prod) = 25679504286205909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_167009
      · exact prime_oneHundredSixtyFiveFG_674391229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25679504286205909) ^ 12839752143102954 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25679504286205909) ^ 8559834762068636 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25679504286205909) ^ 1351552857168732 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25679504286205909) ^ 153761200212 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 25679504286205909) ^ 38078052 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_31723658101780187 : Nat.Prime 31723658101780187 := by
  apply lucas_primality 31723658101780187 (2 : ZMod 31723658101780187)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (71, 1), (167, 1), (36155695577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (71, 1), (167, 1), (36155695577, 1)] : List FactorBlock).map factorBlockValue).prod) = 31723658101780187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_167
      · exact prime_oneHundredSixtyFiveFG_36155695577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31723658101780187) ^ 15861829050890093 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31723658101780187) ^ 857396164912978 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31723658101780187) ^ 446812085940566 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31723658101780187) ^ 189962024561558 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 31723658101780187) ^ 877418 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_33255271536213773 : Nat.Prime 33255271536213773 := by
  apply lucas_primality 33255271536213773 (2 : ZMod 33255271536213773)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (743, 1), (3847, 1), (70942363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (743, 1), (3847, 1), (70942363, 1)] : List FactorBlock).map factorBlockValue).prod) = 33255271536213773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_743
      · exact prime_oneHundredSixtyFiveFG_3847
      · exact prime_oneHundredSixtyFiveFG_70942363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33255271536213773) ^ 16627635768106886 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255271536213773) ^ 811104183810092 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255271536213773) ^ 44758104355604 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255271536213773) ^ 8644468816276 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 33255271536213773) ^ 468764644 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_46811677584201773 : Nat.Prime 46811677584201773 := by
  apply lucas_primality 46811677584201773 (2 : ZMod 46811677584201773)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31, 1), (36479, 1), (940799137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31, 1), (36479, 1), (940799137, 1)] : List FactorBlock).map factorBlockValue).prod) = 46811677584201773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_36479
      · exact prime_oneHundredSixtyFiveFG_940799137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 46811677584201773) ^ 23405838792100886 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46811677584201773) ^ 4255607053109252 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46811677584201773) ^ 1510054115619412 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46811677584201773) ^ 1283250022868 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 46811677584201773) ^ 49757356 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_55651003579448491 : Nat.Prime 55651003579448491 := by
  apply lucas_primality 55651003579448491 (7 : ZMod 55651003579448491)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4051, 1), (223759, 1), (2046487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4051, 1), (223759, 1), (2046487, 1)] : List FactorBlock).map factorBlockValue).prod) = 55651003579448491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_4051
      · exact prime_oneHundredSixtyFiveFG_223759
      · exact prime_oneHundredSixtyFiveFG_2046487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 55651003579448491) ^ 27825501789724245 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 18550334526482830 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 11130200715889698 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 13737596538990 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 248709565110 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 55651003579448491) ^ 27193431270 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_78511797954027271 : Nat.Prime 78511797954027271 := by
  apply lucas_primality 78511797954027271 (3 : ZMod 78511797954027271)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (3457, 1), (8263, 1), (4362719, 1)] : List FactorBlock).map factorBlockValue).prod) = 78511797954027271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_3457
      · exact prime_oneHundredSixtyFiveFG_8263
      · exact prime_oneHundredSixtyFiveFG_4362719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78511797954027271) ^ 39255898977013635 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 26170599318009090 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 15702359590805454 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 11215971136289610 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 22710962671110 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 9501609337290 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 78511797954027271) ^ 17996070330 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_107530895500168793 : Nat.Prime 107530895500168793 := by
  apply lucas_primality 107530895500168793 (3 : ZMod 107530895500168793)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (409, 1), (151579, 1), (12753577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (409, 1), (151579, 1), (12753577, 1)] : List FactorBlock).map factorBlockValue).prod) = 107530895500168793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_409
      · exact prime_oneHundredSixtyFiveFG_151579
      · exact prime_oneHundredSixtyFiveFG_12753577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 107530895500168793) ^ 53765447750084396 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 107530895500168793) ^ 6325346794127576 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 107530895500168793) ^ 262911724939288 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 107530895500168793) ^ 709404967048 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 107530895500168793) ^ 8431430296 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_133962282976311967 : Nat.Prime 133962282976311967 := by
  apply lucas_primality 133962282976311967 (3 : ZMod 133962282976311967)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (463, 1), (4383869460577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (463, 1), (4383869460577, 1)] : List FactorBlock).map factorBlockValue).prod) = 133962282976311967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_463
      · exact prime_oneHundredSixtyFiveFG_4383869460577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 133962282976311967) ^ 66981141488155983 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 44654094325437322 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 12178389361482906 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 289335384398082 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 133962282976311967) ^ 30558 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_145152075582757547 : Nat.Prime 145152075582757547 := by
  apply lucas_primality 145152075582757547 (2 : ZMod 145152075582757547)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (103, 1), (271, 1), (11369, 1), (6181057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (103, 1), (271, 1), (11369, 1), (6181057, 1)] : List FactorBlock).map factorBlockValue).prod) = 145152075582757547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_103
      · exact prime_oneHundredSixtyFiveFG_271
      · exact prime_oneHundredSixtyFiveFG_11369
      · exact prime_oneHundredSixtyFiveFG_6181057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 145152075582757547) ^ 72576037791378773 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 145152075582757547) ^ 3923029069804258 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 145152075582757547) ^ 1409243452259782 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 145152075582757547) ^ 535616515065526 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 145152075582757547) ^ 12767356459034 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 145152075582757547) ^ 23483374378 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_170021964029785961 : Nat.Prime 170021964029785961 := by
  apply lucas_primality 170021964029785961 (3 : ZMod 170021964029785961)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (14078959, 1), (301907911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (14078959, 1), (301907911, 1)] : List FactorBlock).map factorBlockValue).prod) = 170021964029785961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_14078959
      · exact prime_oneHundredSixtyFiveFG_301907911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 170021964029785961) ^ 85010982014892980 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 34004392805957192 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 12076316440 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 170021964029785961) ^ 563158360 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_515381406101720317 : Nat.Prime 515381406101720317 := by
  apply lucas_primality 515381406101720317 (5 : ZMod 515381406101720317)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (2903, 1), (9109, 1), (541387853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (2903, 1), (9109, 1), (541387853, 1)] : List FactorBlock).map factorBlockValue).prod) = 515381406101720317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2903
      · exact prime_oneHundredSixtyFiveFG_9109
      · exact prime_oneHundredSixtyFiveFG_541387853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 515381406101720317) ^ 257690703050860158 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 171793802033906772 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 177534070307172 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 56579361741324 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 515381406101720317) ^ 951963372 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_911676659536508311 : Nat.Prime 911676659536508311 := by
  apply lucas_primality 911676659536508311 (6 : ZMod 911676659536508311)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (15173, 1), (667616203883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (15173, 1), (667616203883, 1)] : List FactorBlock).map factorBlockValue).prod) = 911676659536508311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_15173
      · exact prime_oneHundredSixtyFiveFG_667616203883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 911676659536508311) ^ 455838329768254155 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 303892219845502770 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 182335331907301662 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 60085458349470 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 911676659536508311) ^ 1365570 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_958095564164668681 : Nat.Prime 958095564164668681 := by
  apply lucas_primality 958095564164668681 (13 : ZMod 958095564164668681)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (12601, 1), (791773, 1), (800243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (12601, 1), (791773, 1), (800243, 1)] : List FactorBlock).map factorBlockValue).prod) = 958095564164668681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_12601
      · exact prime_oneHundredSixtyFiveFG_791773
      · exact prime_oneHundredSixtyFiveFG_800243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 958095564164668681) ^ 479047782082334340 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 319365188054889560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 191619112832933736 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 76033296100680 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 1210063445160 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 958095564164668681) ^ 1197255788760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1387430120502120979 : Nat.Prime 1387430120502120979 := by
  apply lucas_primality 1387430120502120979 (7 : ZMod 1387430120502120979)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (823, 1), (991, 1), (1658021921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (823, 1), (991, 1), (1658021921, 1)] : List FactorBlock).map factorBlockValue).prod) = 1387430120502120979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_823
      · exact prime_oneHundredSixtyFiveFG_991
      · exact prime_oneHundredSixtyFiveFG_1658021921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1387430120502120979) ^ 693715060251060489 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1387430120502120979) ^ 462476706834040326 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1387430120502120979) ^ 73022637921164262 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1387430120502120979) ^ 1685820316527486 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1387430120502120979) ^ 1400030394048558 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1387430120502120979) ^ 836798418 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2051946415555650209 : Nat.Prime 2051946415555650209 := by
  apply lucas_primality 2051946415555650209 (6 : ZMod 2051946415555650209)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 2), (1308639295634981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 2), (1308639295634981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2051946415555650209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_1308639295634981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2051946415555650209) ^ 1025973207777825104 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2051946415555650209) ^ 293135202222235744 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (6 : ZMod 2051946415555650209) ^ 1568 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_2858074240329689489 : Nat.Prime 2858074240329689489 := by
  apply lucas_primality 2858074240329689489 (3 : ZMod 2858074240329689489)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (96984187, 1), (1841842939, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (96984187, 1), (1841842939, 1)] : List FactorBlock).map factorBlockValue).prod) = 2858074240329689489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_96984187
      · exact prime_oneHundredSixtyFiveFG_1841842939
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2858074240329689489) ^ 1429037120164844744 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858074240329689489) ^ 29469487024 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 2858074240329689489) ^ 1551746992 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3891887127346728791 : Nat.Prime 3891887127346728791 := by
  apply lucas_primality 3891887127346728791 (7 : ZMod 3891887127346728791)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (29, 1), (523, 1), (2477, 1), (24547, 1), (60289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (29, 1), (523, 1), (2477, 1), (24547, 1), (60289, 1)] : List FactorBlock).map factorBlockValue).prod) = 3891887127346728791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_523
      · exact prime_oneHundredSixtyFiveFG_2477
      · exact prime_oneHundredSixtyFiveFG_24547
      · exact prime_oneHundredSixtyFiveFG_60289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 3891887127346728791) ^ 1945943563673364395 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 778377425469345758 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 555983875335246970 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 134203004391266510 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 7441466782689730 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 1571209982780270 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 158548381771570 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 3891887127346728791) ^ 64553851073110 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_4527184655447032079 : Nat.Prime 4527184655447032079 := by
  apply lucas_primality 4527184655447032079 (7 : ZMod 4527184655447032079)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4527184655447032079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_5821
      · exact prime_oneHundredSixtyFiveFG_152597
      · exact prime_oneHundredSixtyFiveFG_110796689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4527184655447032079) ^ 2263592327723516039 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 196834115454218786 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 777733148161318 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 29667586226774 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 40860288302 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8164773535422159913 : Nat.Prime 8164773535422159913 := by
  apply lucas_primality 8164773535422159913 (5 : ZMod 8164773535422159913)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (72522847, 1), (4690920329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (72522847, 1), (4690920329, 1)] : List FactorBlock).map factorBlockValue).prod) = 8164773535422159913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_72522847
      · exact prime_oneHundredSixtyFiveFG_4690920329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 8164773535422159913) ^ 4082386767711079956 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8164773535422159913) ^ 2721591178474053304 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8164773535422159913) ^ 112582087896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 8164773535422159913) ^ 1740548328 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_11350910713036676963 : Nat.Prime 11350910713036676963 := by
  apply lucas_primality 11350910713036676963 (2 : ZMod 11350910713036676963)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (173897, 1), (694401681959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (173897, 1), (694401681959, 1)] : List FactorBlock).map factorBlockValue).prod) = 11350910713036676963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_173897
      · exact prime_oneHundredSixtyFiveFG_694401681959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11350910713036676963) ^ 5675455356518338481 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11350910713036676963) ^ 241508738575248446 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11350910713036676963) ^ 65273758104146 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 11350910713036676963) ^ 16346318 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_17551666958773228451 : Nat.Prime 17551666958773228451 := by
  apply lucas_primality 17551666958773228451 (2 : ZMod 17551666958773228451)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (73, 1), (1167811, 1), (316744871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (73, 1), (1167811, 1), (316744871, 1)] : List FactorBlock).map factorBlockValue).prod) = 17551666958773228451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_1167811
      · exact prime_oneHundredSixtyFiveFG_316744871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17551666958773228451) ^ 8775833479386614225 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17551666958773228451) ^ 3510333391754645690 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17551666958773228451) ^ 1350128227597940650 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17551666958773228451) ^ 240433793955797650 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17551666958773228451) ^ 15029544128950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 17551666958773228451) ^ 55412631950 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_28190581847848388867 : Nat.Prime 28190581847848388867 := by
  apply lucas_primality 28190581847848388867 (2 : ZMod 28190581847848388867)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (95533027, 1), (147543643979, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (95533027, 1), (147543643979, 1)] : List FactorBlock).map factorBlockValue).prod) = 28190581847848388867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_95533027
      · exact prime_oneHundredSixtyFiveFG_147543643979
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 28190581847848388867) ^ 14095290923924194433 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 28190581847848388867) ^ 295087287958 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 28190581847848388867) ^ 191066054 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_35653477162396384699 : Nat.Prime 35653477162396384699 := by
  apply lucas_primality 35653477162396384699 (3 : ZMod 35653477162396384699)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (229, 1), (1523, 1), (847991, 1), (1826549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (229, 1), (1523, 1), (847991, 1), (1826549, 1)] : List FactorBlock).map factorBlockValue).prod) = 35653477162396384699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_229
      · exact prime_oneHundredSixtyFiveFG_1523
      · exact prime_oneHundredSixtyFiveFG_847991
      · exact prime_oneHundredSixtyFiveFG_1826549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35653477162396384699) ^ 17826738581198192349 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 11884492387465461566 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 3241225196581489518 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 155692040010464562 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 23410030966773726 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 42044640995478 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35653477162396384699) ^ 19519584288402 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_36265159998777480317 : Nat.Prime 36265159998777480317 := by
  apply lucas_primality 36265159998777480317 (5 : ZMod 36265159998777480317)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36265159998777480317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_29
      · exact prime_oneHundredSixtyFiveFG_73
      · exact prime_oneHundredSixtyFiveFG_47061672383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36265159998777480317) ^ 18132579999388740158 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 5180737142682497188 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 2789627692213652332 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 1250522758578533804 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 496783013681883292 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 770588 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_2063
      · exact prime_oneHundredSixtyFiveFG_15269
      · exact prime_oneHundredSixtyFiveFG_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_89994286861309679141 : Nat.Prime 89994286861309679141 := by
  apply lucas_primality 89994286861309679141 (2 : ZMod 89994286861309679141)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (145152075582757547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (145152075582757547, 1)] : List FactorBlock).map factorBlockValue).prod) = 89994286861309679141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_145152075582757547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89994286861309679141) ^ 44997143430654839570 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 89994286861309679141) ^ 17998857372261935828 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 89994286861309679141) ^ 2903041511655150940 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 89994286861309679141) ^ 620 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_137030878047549266579 : Nat.Prime 137030878047549266579 := by
  apply lucas_primality 137030878047549266579 (2 : ZMod 137030878047549266579)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (47, 2), (34171, 1), (129669250493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (47, 2), (34171, 1), (129669250493, 1)] : List FactorBlock).map factorBlockValue).prod) = 137030878047549266579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_47
      · exact prime_oneHundredSixtyFiveFG_34171
      · exact prime_oneHundredSixtyFiveFG_129669250493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 137030878047549266579) ^ 68515439023774633289 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137030878047549266579) ^ 19575839721078466654 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137030878047549266579) ^ 2915550596756367374 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137030878047549266579) ^ 4010151240746518 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 137030878047549266579) ^ 1056772346 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_224952136074415902667 : Nat.Prime 224952136074415902667 := by
  apply lucas_primality 224952136074415902667 (3 : ZMod 224952136074415902667)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (19853, 1), (100271, 1), (355354249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (19853, 1), (100271, 1), (355354249, 1)] : List FactorBlock).map factorBlockValue).prod) = 224952136074415902667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_53
      · exact prime_oneHundredSixtyFiveFG_19853
      · exact prime_oneHundredSixtyFiveFG_100271
      · exact prime_oneHundredSixtyFiveFG_355354249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 224952136074415902667) ^ 112476068037207951333 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 74984045358138634222 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 4244379925932375522 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 11330888836670322 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 2243441633916246 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 224952136074415902667) ^ 633036291834 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_6863
      · exact prime_oneHundredSixtyFiveFG_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_277042283689663805783 : Nat.Prime 277042283689663805783 := by
  apply lucas_primality 277042283689663805783 (5 : ZMod 277042283689663805783)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2327173, 1), (8503336257881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2327173, 1), (8503336257881, 1)] : List FactorBlock).map factorBlockValue).prod) = 277042283689663805783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_2327173
      · exact prime_oneHundredSixtyFiveFG_8503336257881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277042283689663805783) ^ 138521141844831902891 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 39577469098523400826 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 119046707610334 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 277042283689663805783) ^ 32580422 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_516843125390944643623 : Nat.Prime 516843125390944643623 := by
  apply lucas_primality 516843125390944643623 (3 : ZMod 516843125390944643623)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1076762003, 1), (4210504841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1076762003, 1), (4210504841, 1)] : List FactorBlock).map factorBlockValue).prod) = 516843125390944643623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_1076762003
      · exact prime_oneHundredSixtyFiveFG_4210504841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 516843125390944643623) ^ 258421562695472321811 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 172281041796981547874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 27202269757418139138 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 479997551874 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 516843125390944643623) ^ 122750868342 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_689580321364101784147 : Nat.Prime 689580321364101784147 := by
  apply lucas_primality 689580321364101784147 (2 : ZMod 689580321364101784147)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (223, 1), (515381406101720317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (223, 1), (515381406101720317, 1)] : List FactorBlock).map factorBlockValue).prod) = 689580321364101784147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_223
      · exact prime_oneHundredSixtyFiveFG_515381406101720317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 689580321364101784147) ^ 344790160682050892073 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 229860107121367261382 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 3092288436610321902 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 689580321364101784147) ^ 1338 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_733814796752556207677 : Nat.Prime 733814796752556207677 := by
  apply lucas_primality 733814796752556207677 (2 : ZMod 733814796752556207677)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (170021964029785961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (170021964029785961, 1)] : List FactorBlock).map factorBlockValue).prod) = 733814796752556207677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_83
      · exact prime_oneHundredSixtyFiveFG_170021964029785961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 733814796752556207677) ^ 366907398376278103838 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 56447292057888939052 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 8841142129548869972 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 733814796752556207677) ^ 4316 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_829821849978416232493 : Nat.Prime 829821849978416232493 := by
  apply lucas_primality 829821849978416232493 (5 : ZMod 829821849978416232493)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) = 829821849978416232493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_127
      · exact prime_oneHundredSixtyFiveFG_947
      · exact prime_oneHundredSixtyFiveFG_11437
      · exact prime_oneHundredSixtyFiveFG_1861975811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829821849978416232493) ^ 414910924989208116246 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 276607283326138744164 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 6534030314790678996 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 876263833134547236 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 72555901895463516 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 445667363172 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_199
      · exact prime_oneHundredSixtyFiveFG_52864081
      · exact prime_oneHundredSixtyFiveFG_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1088203351443940163963 : Nat.Prime 1088203351443940163963 := by
  apply lucas_primality 1088203351443940163963 (2 : ZMod 1088203351443940163963)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (17551666958773228451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (17551666958773228451, 1)] : List FactorBlock).map factorBlockValue).prod) = 1088203351443940163963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_17551666958773228451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1088203351443940163963) ^ 544101675721970081981 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088203351443940163963) ^ 35103333917546456902 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1088203351443940163963) ^ 62 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1550411355806685423811 : Nat.Prime 1550411355806685423811 := by
  apply lucas_primality 1550411355806685423811 (2 : ZMod 1550411355806685423811)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (3283807, 1), (476907466417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1550411355806685423811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_3283807
      · exact prime_oneHundredSixtyFiveFG_476907466417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1550411355806685423811) ^ 775205677903342711905 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 516803785268895141270 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 310082271161337084762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 140946486891516856710 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 472138391752830 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 1550411355806685423811) ^ 3250968930 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1566189032198506322689 : Nat.Prime 1566189032198506322689 := by
  apply lucas_primality 1566189032198506322689 (7 : ZMod 1566189032198506322689)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (211, 1), (5521, 1), (583527732737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (211, 1), (5521, 1), (583527732737, 1)] : List FactorBlock).map factorBlockValue).prod) = 1566189032198506322689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_211
      · exact prime_oneHundredSixtyFiveFG_5521
      · exact prime_oneHundredSixtyFiveFG_583527732737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1566189032198506322689) ^ 783094516099253161344 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 522063010732835440896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 7422696835064011008 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 283678506103696128 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 1566189032198506322689) ^ 2684001024 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3019418713742564280571 : Nat.Prime 3019418713742564280571 := by
  apply lucas_primality 3019418713742564280571 (10 : ZMod 3019418713742564280571)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019418713742564280571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_97
      · exact prime_oneHundredSixtyFiveFG_4671071
      · exact prime_oneHundredSixtyFiveFG_222133410637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019418713742564280571) ^ 1509709356871282140285 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 1006472904580854760190 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 603883742748512856114 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 31128027976727466810 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 646408224953670 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 13592816610 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5000910483656400298243 : Nat.Prime 5000910483656400298243 := by
  apply lucas_primality 5000910483656400298243 (2 : ZMod 5000910483656400298243)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (881, 1), (55651003579448491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (881, 1), (55651003579448491, 1)] : List FactorBlock).map factorBlockValue).prod) = 5000910483656400298243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_881
      · exact prime_oneHundredSixtyFiveFG_55651003579448491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5000910483656400298243) ^ 2500455241828200149121 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 1666970161218800099414 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 294171204920964723426 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 5676402365103746082 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5000910483656400298243) ^ 89862 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5107835118109486565689 : Nat.Prime 5107835118109486565689 := by
  apply lucas_primality 5107835118109486565689 (7 : ZMod 5107835118109486565689)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (339679, 1), (626551724582803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (339679, 1), (626551724582803, 1)] : List FactorBlock).map factorBlockValue).prod) = 5107835118109486565689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_339679
      · exact prime_oneHundredSixtyFiveFG_626551724582803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5107835118109486565689) ^ 2553917559054743282844 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5107835118109486565689) ^ 1702611706036495521896 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5107835118109486565689) ^ 15037241389987272 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 5107835118109486565689) ^ 8152296 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_5915082252478265715067 : Nat.Prime 5915082252478265715067 := by
  apply lucas_primality 5915082252478265715067 (2 : ZMod 5915082252478265715067)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1297, 1), (2003, 1), (4373, 1), (50123, 1), (91121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1297, 1), (2003, 1), (4373, 1), (50123, 1), (91121, 1)] : List FactorBlock).map factorBlockValue).prod) = 5915082252478265715067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_1297
      · exact prime_oneHundredSixtyFiveFG_2003
      · exact prime_oneHundredSixtyFiveFG_4373
      · exact prime_oneHundredSixtyFiveFG_50123
      · exact prime_oneHundredSixtyFiveFG_91121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5915082252478265715067) ^ 2957541126239132857533 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 1971694084159421905022 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 311320118551487669214 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 4560587704300898778 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 2953111459050557022 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 1352637148977421842 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 118011337160151342 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 5915082252478265715067) ^ 64914588870603546 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8695344076653562208641 : Nat.Prime 8695344076653562208641 := by
  apply lucas_primality 8695344076653562208641 (7 : ZMod 8695344076653562208641)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 3), (5, 1), (11527, 1), (2668993, 1), (16356083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 3), (5, 1), (11527, 1), (2668993, 1), (16356083, 1)] : List FactorBlock).map factorBlockValue).prod) = 8695344076653562208641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11527
      · exact prime_oneHundredSixtyFiveFG_2668993
      · exact prime_oneHundredSixtyFiveFG_16356083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8695344076653562208641) ^ 4347672038326781104320 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 2898448025551187402880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 1739068815330712441728 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 754345803474760320 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 3257911907844480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 8695344076653562208641) ^ 531627534334080 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_8993759679696815118617 : Nat.Prime 8993759679696815118617 := by
  apply lucas_primality 8993759679696815118617 (3 : ZMod 8993759679696815118617)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993759679696815118617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_36265159998777480317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8993759679696815118617) ^ 4496879839848407559308 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 290121279990219842536 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 248 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_10632020445244221866299 : Nat.Prime 10632020445244221866299 := by
  apply lucas_primality 10632020445244221866299 (2 : ZMod 10632020445244221866299)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (241643, 1), (2444382011949727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (241643, 1), (2444382011949727, 1)] : List FactorBlock).map factorBlockValue).prod) = 10632020445244221866299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_241643
      · exact prime_oneHundredSixtyFiveFG_2444382011949727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10632020445244221866299) ^ 5316010222622110933149 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10632020445244221866299) ^ 3544006815081407288766 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10632020445244221866299) ^ 43998876215095086 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 10632020445244221866299) ^ 4349574 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_35853529750253765128927 : Nat.Prime 35853529750253765128927 := by
  apply lucas_primality 35853529750253765128927 (3 : ZMod 35853529750253765128927)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (17, 1), (71, 1), (8317, 1), (66139999399751, 1)] : List FactorBlock).map factorBlockValue).prod) = 35853529750253765128927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_8317
      · exact prime_oneHundredSixtyFiveFG_66139999399751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 35853529750253765128927) ^ 17926764875126882564463 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 11951176583417921709642 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 2109031161779633242878 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 504979292257095283506 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 4310872880876970678 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 35853529750253765128927) ^ 542085426 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_48724766310286365550171 : Nat.Prime 48724766310286365550171 := by
  apply lucas_primality 48724766310286365550171 (2 : ZMod 48724766310286365550171)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (20719, 1), (119047, 1), (773769673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (23, 1), (37, 1), (20719, 1), (119047, 1), (773769673, 1)] : List FactorBlock).map factorBlockValue).prod) = 48724766310286365550171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_20719
      · exact prime_oneHundredSixtyFiveFG_119047
      · exact prime_oneHundredSixtyFiveFG_773769673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 48724766310286365550171) ^ 24362383155143182775085 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 16241588770095455183390 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 9744953262057273110034 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 2118468100447233284790 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 1316885575953685555410 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 2351694884419439430 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 409290165315265110 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 48724766310286365550171) ^ 62970633265290 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_50418713460813862866463 : Nat.Prime 50418713460813862866463 := by
  apply lucas_primality 50418713460813862866463 (5 : ZMod 50418713460813862866463)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (17, 1), (74843, 1), (2159147, 1), (37763581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (17, 1), (74843, 1), (2159147, 1), (37763581, 1)] : List FactorBlock).map factorBlockValue).prod) = 50418713460813862866463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_74843
      · exact prime_oneHundredSixtyFiveFG_2159147
      · exact prime_oneHundredSixtyFiveFG_37763581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 50418713460813862866463) ^ 25209356730406931433231 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 16806237820271287622154 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 2965806674165521345086 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 673659707131112634 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 23351218541773146 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 50418713460813862866463) ^ 1335114735565302 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_54300705579177180686021 : Nat.Prime 54300705579177180686021 := by
  apply lucas_primality 54300705579177180686021 (10 : ZMod 54300705579177180686021)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (31, 1), (37, 1), (593, 1), (3991695145719031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (31, 1), (37, 1), (593, 1), (3991695145719031, 1)] : List FactorBlock).map factorBlockValue).prod) = 54300705579177180686021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_593
      · exact prime_oneHundredSixtyFiveFG_3991695145719031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 54300705579177180686021) ^ 27150352789588590343010 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 54300705579177180686021) ^ 10860141115835436137204 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 54300705579177180686021) ^ 1751635663844425183420 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 54300705579177180686021) ^ 1467586637275058937460 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 54300705579177180686021) ^ 91569486642794571140 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (10 : ZMod 54300705579177180686021) ^ 13603420 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_169042064994073381940659 : Nat.Prime 169042064994073381940659 := by
  apply lucas_primality 169042064994073381940659 (2 : ZMod 169042064994073381940659)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (139, 1), (877, 1), (25679504286205909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (139, 1), (877, 1), (25679504286205909, 1)] : List FactorBlock).map factorBlockValue).prod) = 169042064994073381940659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_139
      · exact prime_oneHundredSixtyFiveFG_877
      · exact prime_oneHundredSixtyFiveFG_25679504286205909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 169042064994073381940659) ^ 84521032497036690970329 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 169042064994073381940659) ^ 56347354998024460646886 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 169042064994073381940659) ^ 1216129963986139438422 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 169042064994073381940659) ^ 192750359172261552954 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 169042064994073381940659) ^ 6582762 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_215121178501522590773563 : Nat.Prime 215121178501522590773563 := by
  apply lucas_primality 215121178501522590773563 (2 : ZMod 215121178501522590773563)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (35853529750253765128927, 1)] : List FactorBlock).map factorBlockValue).prod) = 215121178501522590773563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_35853529750253765128927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 215121178501522590773563) ^ 107560589250761295386781 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 71707059500507530257854 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 215121178501522590773563) ^ 6 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_224548754488655613705599 : Nat.Prime 224548754488655613705599 := by
  apply lucas_primality 224548754488655613705599 (11 : ZMod 224548754488655613705599)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (17, 1), (23, 1), (31, 1), (14541284492348387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (17, 1), (23, 1), (31, 1), (14541284492348387, 1)] : List FactorBlock).map factorBlockValue).prod) = 224548754488655613705599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_13
      · exact prime_oneHundredSixtyFiveFG_17
      · exact prime_oneHundredSixtyFiveFG_23
      · exact prime_oneHundredSixtyFiveFG_31
      · exact prime_oneHundredSixtyFiveFG_14541284492348387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 224548754488655613705599) ^ 112274377244327806852799 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 32078393498379373386514 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 17272981114511970285046 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 13208750264038565512094 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 9762989325593722335026 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 7243508209311471409858 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (11 : ZMod 224548754488655613705599) ^ 15442154 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_259193266026634557332219 : Nat.Prime 259193266026634557332219 := by
  apply lucas_primality 259193266026634557332219 (2 : ZMod 259193266026634557332219)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) = 259193266026634557332219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_71
      · exact prime_oneHundredSixtyFiveFG_19471
      · exact prime_oneHundredSixtyFiveFG_273308408322643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259193266026634557332219) ^ 129596633013317278666109 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 37027609432376365333174 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 3650609380656824751158 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 13311759335762649958 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 948354526 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_270729353794970093039171 : Nat.Prime 270729353794970093039171 := by
  apply lucas_primality 270729353794970093039171 (2 : ZMod 270729353794970093039171)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (11, 1), (36697, 1), (1368724432009199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (11, 1), (36697, 1), (1368724432009199, 1)] : List FactorBlock).map factorBlockValue).prod) = 270729353794970093039171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_36697
      · exact prime_oneHundredSixtyFiveFG_1368724432009199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 270729353794970093039171) ^ 135364676897485046519585 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 54145870758994018607834 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 38675621970710013291310 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 24611759435906372094470 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 7377424688529582610 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 270729353794970093039171) ^ 197796830 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_501444733170615953101543 : Nat.Prime 501444733170615953101543 := by
  apply lucas_primality 501444733170615953101543 (3 : ZMod 501444733170615953101543)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (7829, 1), (33255271536213773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (7829, 1), (33255271536213773, 1)] : List FactorBlock).map factorBlockValue).prod) = 501444733170615953101543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_107
      · exact prime_oneHundredSixtyFiveFG_7829
      · exact prime_oneHundredSixtyFiveFG_33255271536213773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 501444733170615953101543) ^ 250722366585307976550771 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 501444733170615953101543) ^ 167148244390205317700514 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 501444733170615953101543) ^ 4686399375426317318706 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 501444733170615953101543) ^ 64049652978747726798 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 501444733170615953101543) ^ 15078654 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_724395956348371658049161 : Nat.Prime 724395956348371658049161 := by
  apply lucas_primality 724395956348371658049161 (3 : ZMod 724395956348371658049161)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (11, 1), (59723, 1), (536563, 1), (7339440673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (11, 1), (59723, 1), (536563, 1), (7339440673, 1)] : List FactorBlock).map factorBlockValue).prod) = 724395956348371658049161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_59723
      · exact prime_oneHundredSixtyFiveFG_536563
      · exact prime_oneHundredSixtyFiveFG_7339440673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 724395956348371658049161) ^ 362197978174185829024580 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 144879191269674331609832 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 103485136621195951149880 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 65854177849851968913560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 12129262701946848920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 1350066919165823320 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 724395956348371658049161) ^ 98699068310920 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_983533507497054051322853 : Nat.Prime 983533507497054051322853 := by
  apply lucas_primality 983533507497054051322853 (2 : ZMod 983533507497054051322853)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (643, 1), (2843, 1), (149173, 1), (20969238383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (643, 1), (2843, 1), (149173, 1), (20969238383, 1)] : List FactorBlock).map factorBlockValue).prod) = 983533507497054051322853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_43
      · exact prime_oneHundredSixtyFiveFG_643
      · exact prime_oneHundredSixtyFiveFG_2843
      · exact prime_oneHundredSixtyFiveFG_149173
      · exact prime_oneHundredSixtyFiveFG_20969238383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 983533507497054051322853) ^ 491766753748527025661426 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 22872872267373350030764 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 1529601100306460421964 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 345949176045393616364 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 6593240784170419924 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 983533507497054051322853) ^ 46903635198044 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1650763597780910034012919 : Nat.Prime 1650763597780910034012919 := by
  apply lucas_primality 1650763597780910034012919 (3 : ZMod 1650763597780910034012919)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (571, 1), (1327, 1), (12292349, 1), (29538723241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (571, 1), (1327, 1), (12292349, 1), (29538723241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1650763597780910034012919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_571
      · exact prime_oneHundredSixtyFiveFG_1327
      · exact prime_oneHundredSixtyFiveFG_12292349
      · exact prime_oneHundredSixtyFiveFG_29538723241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1650763597780910034012919) ^ 825381798890455017006459 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650763597780910034012919) ^ 550254532593636678004306 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650763597780910034012919) ^ 2891004549528739113858 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650763597780910034012919) ^ 1243981610987874931434 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650763597780910034012919) ^ 134291956548004782 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 1650763597780910034012919) ^ 55884730843398 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_3940411987980561962981753 : Nat.Prime 3940411987980561962981753 := by
  apply lucas_primality 3940411987980561962981753 (3 : ZMod 3940411987980561962981753)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (953, 1), (516843125390944643623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (953, 1), (516843125390944643623, 1)] : List FactorBlock).map factorBlockValue).prod) = 3940411987980561962981753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_953
      · exact prime_oneHundredSixtyFiveFG_516843125390944643623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3940411987980561962981753) ^ 1970205993990280981490876 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3940411987980561962981753) ^ 4134745003127557148984 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 3940411987980561962981753) ^ 7624 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_14849207267790644784910913 : Nat.Prime 14849207267790644784910913 := by
  apply lucas_primality 14849207267790644784910913 (3 : ZMod 14849207267790644784910913)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (131, 1), (349, 1), (461, 1), (93947437, 1), (117176551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (131, 1), (349, 1), (461, 1), (93947437, 1), (117176551, 1)] : List FactorBlock).map factorBlockValue).prod) = 14849207267790644784910913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_131
      · exact prime_oneHundredSixtyFiveFG_349
      · exact prime_oneHundredSixtyFiveFG_461
      · exact prime_oneHundredSixtyFiveFG_93947437
      · exact prime_oneHundredSixtyFiveFG_117176551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 14849207267790644784910913) ^ 7424603633895322392455456 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 113352727235043089961152 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 42547871827480357549888 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 32210861752257363958592 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 158058673466426176 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 14849207267790644784910913) ^ 126725075461477312 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_15414779603079075506864849 : Nat.Prime 15414779603079075506864849 := by
  apply lucas_primality 15414779603079075506864849 (3 : ZMod 15414779603079075506864849)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (43, 1), (61, 1), (179, 1), (2051946415555650209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (43, 1), (61, 1), (179, 1), (2051946415555650209, 1)] : List FactorBlock).map factorBlockValue).prod) = 15414779603079075506864849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_43
      · exact prime_oneHundredSixtyFiveFG_61
      · exact prime_oneHundredSixtyFiveFG_179
      · exact prime_oneHundredSixtyFiveFG_2051946415555650209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15414779603079075506864849) ^ 7707389801539537753432424 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 358483246583234314113136 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 252701304968509434538768 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 86116087168039527971312 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 15414779603079075506864849) ^ 7512272 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_26247851974833920955244169 : Nat.Prime 26247851974833920955244169 := by
  apply lucas_primality 26247851974833920955244169 (13 : ZMod 26247851974833920955244169)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (83, 1), (1451, 1), (3891887127346728791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (83, 1), (1451, 1), (3891887127346728791, 1)] : List FactorBlock).map factorBlockValue).prod) = 26247851974833920955244169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_7
      · exact prime_oneHundredSixtyFiveFG_83
      · exact prime_oneHundredSixtyFiveFG_1451
      · exact prime_oneHundredSixtyFiveFG_3891887127346728791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 26247851974833920955244169) ^ 13123925987416960477622084 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 26247851974833920955244169) ^ 3749693139261988707892024 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 26247851974833920955244169) ^ 316239180419685794641496 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 26247851974833920955244169) ^ 18089491367907595420568 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (13 : ZMod 26247851974833920955244169) ^ 6744248 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_100709362868851678130807777 : Nat.Prime 100709362868851678130807777 := by
  apply lucas_primality 100709362868851678130807777 (3 : ZMod 100709362868851678130807777)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (97, 1), (349, 1), (5113145897, 1), (18181701523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (97, 1), (349, 1), (5113145897, 1), (18181701523, 1)] : List FactorBlock).map factorBlockValue).prod) = 100709362868851678130807777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_97
      · exact prime_oneHundredSixtyFiveFG_349
      · exact prime_oneHundredSixtyFiveFG_5113145897
      · exact prime_oneHundredSixtyFiveFG_18181701523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100709362868851678130807777) ^ 50354681434425839065403888 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100709362868851678130807777) ^ 1038240854318058537431008 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100709362868851678130807777) ^ 288565509652870137910624 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100709362868851678130807777) ^ 19696164533059808 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 100709362868851678130807777) ^ 5539050497636512 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_344045918654260494778438561 : Nat.Prime 344045918654260494778438561 := by
  apply lucas_primality 344045918654260494778438561 (7 : ZMod 344045918654260494778438561)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (5, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (5, 1), (89, 1), (131, 1), (1031, 1), (11352647, 1), (1750801123, 1)] : List FactorBlock).map factorBlockValue).prod) = 344045918654260494778438561 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_89
      · exact prime_oneHundredSixtyFiveFG_131
      · exact prime_oneHundredSixtyFiveFG_1031
      · exact prime_oneHundredSixtyFiveFG_11352647
      · exact prime_oneHundredSixtyFiveFG_1750801123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 344045918654260494778438561) ^ 172022959327130247389219280 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 114681972884753498259479520 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 68809183730852098955687712 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 3865684479261353873915040 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 2626304722551606830369760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 333701182011891847505760 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 30305348052684144480 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 344045918654260494778438561) ^ 196507709604810720 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_806091057342833473303201091 : Nat.Prime 806091057342833473303201091 := by
  apply lucas_primality 806091057342833473303201091 (2 : ZMod 806091057342833473303201091)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) = 806091057342833473303201091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_311
      · exact prime_oneHundredSixtyFiveFG_259193266026634557332219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 806091057342833473303201091) ^ 403045528671416736651600545 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 161218211468566694660640218 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 2591932660266345573322190 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 3110 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_1990551386499650005503823103 : Nat.Prime 1990551386499650005503823103 := by
  apply lucas_primality 1990551386499650005503823103 (5 : ZMod 1990551386499650005503823103)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (216973, 1), (24455819, 1), (4362013817011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (216973, 1), (24455819, 1), (4362013817011, 1)] : List FactorBlock).map factorBlockValue).prod) = 1990551386499650005503823103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_43
      · exact prime_oneHundredSixtyFiveFG_216973
      · exact prime_oneHundredSixtyFiveFG_24455819
      · exact prime_oneHundredSixtyFiveFG_4362013817011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1990551386499650005503823103) ^ 995275693249825002751911551 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1990551386499650005503823103) ^ 46291892709294186174507514 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1990551386499650005503823103) ^ 9174189353051531782774 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1990551386499650005503823103) ^ 81393773256976182458 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (5 : ZMod 1990551386499650005503823103) ^ 456337707766282 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_6502467862565523351312488803 : Nat.Prime 6502467862565523351312488803 := by
  apply lucas_primality 6502467862565523351312488803 (2 : ZMod 6502467862565523351312488803)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 6502467862565523351312488803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_107
      · exact prime_oneHundredSixtyFiveFG_43001837
      · exact prime_oneHundredSixtyFiveFG_78511797954027271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6502467862565523351312488803) ^ 3251233931282761675656244401 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 2167489287521841117104162934 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 60770727687528255619742886 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 151213722859456523946 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 6502467862565523351312488803) ^ 82821538062 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_12192127242310356283710916501 : Nat.Prime 12192127242310356283710916501 := by
  apply lucas_primality 12192127242310356283710916501 (2 : ZMod 12192127242310356283710916501)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 12192127242310356283710916501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_171401
      · exact prime_oneHundredSixtyFiveFG_714027719
      · exact prime_oneHundredSixtyFiveFG_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 12192127242310356283710916501) ^ 6096063621155178141855458250 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 4064042414103452094570305500 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 2438425448462071256742183300 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 1108375203846396025791901500 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 71132182672856962816500 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 17075145569118103500 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 12192127242310356283710916501) ^ 2019353573561263500 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_27867719410995100077053523439 : Nat.Prime 27867719410995100077053523439 := by
  apply lucas_primality 27867719410995100077053523439 (3 : ZMod 27867719410995100077053523439)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 27867719410995100077053523439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_19
      · exact prime_oneHundredSixtyFiveFG_41
      · exact prime_oneHundredSixtyFiveFG_397
      · exact prime_oneHundredSixtyFiveFG_13617913
      · exact prime_oneHundredSixtyFiveFG_100257985466497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27867719410995100077053523439) ^ 13933859705497550038526761719 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 9289239803665033359017841146 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 2533429037363190916095774858 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 1466722074262900004055448602 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 679700473438904879928134718 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 70195766778325189110966054 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 2046401633715467272926 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (3 : ZMod 27867719410995100077053523439) ^ 277960097455854 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_39014807175393140107874932801 : Nat.Prime 39014807175393140107874932801 := by
  apply lucas_primality 39014807175393140107874932801 (7 : ZMod 39014807175393140107874932801)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 2), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 39014807175393140107874932801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_171401
      · exact prime_oneHundredSixtyFiveFG_714027719
      · exact prime_oneHundredSixtyFiveFG_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 39014807175393140107874932801) ^ 19507403587696570053937466400 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 13004935725131046702624977600 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 7802961435078628021574986560 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 3546800652308467282534084800 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 227622984553142281012800 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 54640465821177931200 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (7 : ZMod 39014807175393140107874932801) ^ 6461931435396043200 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_97537017938482850269687332037 : Nat.Prime 97537017938482850269687332037 := by
  apply lucas_primality 97537017938482850269687332037 (2 : ZMod 97537017938482850269687332037)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1625321, 1), (5000910483656400298243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1625321, 1), (5000910483656400298243, 1)] : List FactorBlock).map factorBlockValue).prod) = 97537017938482850269687332037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_1625321
      · exact prime_oneHundredSixtyFiveFG_5000910483656400298243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 97537017938482850269687332037) ^ 48768508969241425134843666018 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 97537017938482850269687332037) ^ 32512339312827616756562444012 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 97537017938482850269687332037) ^ 60010925803876803578916 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 97537017938482850269687332037) ^ 19503852 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_195074035876965700539374664001 : Nat.Prime 195074035876965700539374664001 := by
  apply lucas_primality 195074035876965700539374664001 (14 : ZMod 195074035876965700539374664001)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664001 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_5
      · exact prime_oneHundredSixtyFiveFG_11
      · exact prime_oneHundredSixtyFiveFG_171401
      · exact prime_oneHundredSixtyFiveFG_714027719
      · exact prime_oneHundredSixtyFiveFG_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 195074035876965700539374664001) ^ 97537017938482850269687332000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 65024678625655233513124888000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 39014807175393140107874932800 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 17734003261542336412670424000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 1138114922765711405064000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 273202329105889656000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (14 : ZMod 195074035876965700539374664001) ^ 32309657176980216000 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem prime_oneHundredSixtyFiveFG_195074035876965700539374664019 : Nat.Prime 195074035876965700539374664019 := by
  apply lucas_primality 195074035876965700539374664019 (2 : ZMod 195074035876965700539374664019)
  · rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (223, 1), (3940411987980561962981753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (223, 1), (3940411987980561962981753, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSixtyFiveFG_2
      · exact prime_oneHundredSixtyFiveFG_3
      · exact prime_oneHundredSixtyFiveFG_37
      · exact prime_oneHundredSixtyFiveFG_223
      · exact prime_oneHundredSixtyFiveFG_3940411987980561962981753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 195074035876965700539374664019) ^ 97537017938482850269687332009 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 195074035876965700539374664019) ^ 65024678625655233513124888006 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 195074035876965700539374664019) ^ 5272271239917991906469585514 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 195074035876965700539374664019) ^ 874771461331684755781949166 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide
    · change (2 : ZMod 195074035876965700539374664019) ^ 49506 ≠ 1
      rw [← oneHundredSixtyFiveFGFastPow_eq_pow]
      decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664000 : Nat.totient 195074035876965700539374664000 = 47290399383401874189158400000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 3), (11, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_171401, prime_oneHundredSixtyFiveFG_714027719, prime_oneHundredSixtyFiveFG_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664001 : Nat.totient 195074035876965700539374664001 = 195074035876965700539374664000 := by
  rw [← show ((([(195074035876965700539374664001, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_195074035876965700539374664001]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664002 : Nat.totient 195074035876965700539374664002 = 97536922609301949099132525312 := by
  rw [← show ((([(2, 1), (1023313, 1), (6852793069, 1), (13908918562933, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_1023313, prime_oneHundredSixtyFiveFG_6852793069, prime_oneHundredSixtyFiveFG_13908918562933]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664003 : Nat.totient 195074035876965700539374664003 = 111459852908769410377997276160 := by
  rw [← show ((([(3, 1), (7, 1), (10111, 1), (5121009329, 1), (179403328798297, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_10111, prime_oneHundredSixtyFiveFG_5121009329, prime_oneHundredSixtyFiveFG_179403328798297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664004 : Nat.totient 195074035876965700539374664004 = 96833346262848713535719283360 := by
  rw [← show ((([(2, 2), (139, 1), (72911, 1), (151687, 1), (31723658101780187, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_139, prime_oneHundredSixtyFiveFG_72911, prime_oneHundredSixtyFiveFG_151687, prime_oneHundredSixtyFiveFG_31723658101780187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664005 : Nat.totient 195074035876965700539374664005 = 156059228701572560431499731200 := by
  rw [← show ((([(5, 1), (39014807175393140107874932801, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_39014807175393140107874932801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664006 : Nat.totient 195074035876965700539374664006 = 61876298112390873873216000000 := by
  rw [← show ((([(2, 1), (3, 5), (31, 1), (61, 1), (3251, 1), (371387, 1), (5760091, 1), (30520993, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_31, prime_oneHundredSixtyFiveFG_61, prime_oneHundredSixtyFiveFG_3251, prime_oneHundredSixtyFiveFG_371387, prime_oneHundredSixtyFiveFG_5760091, prime_oneHundredSixtyFiveFG_30520993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664007 : Nat.totient 195074035876965700539374664007 = 183599092590030392794470682752 := by
  rw [← show ((([(17, 1), (3343093065173, 1), (3432433098085627, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_3343093065173, prime_oneHundredSixtyFiveFG_3432433098085627]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664008 : Nat.totient 195074035876965700539374664008 = 97432026530583514585866351616 := by
  rw [← show ((([(2, 3), (929, 1), (26247851974833920955244169, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_929, prime_oneHundredSixtyFiveFG_26247851974833920955244169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664009 : Nat.totient 195074035876965700539374664009 = 123204627820750917248466310080 := by
  rw [← show ((([(3, 1), (19, 1), (4663781, 1), (733814796752556207677, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_19, prime_oneHundredSixtyFiveFG_4663781, prime_oneHundredSixtyFiveFG_733814796752556207677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664010 : Nat.totient 195074035876965700539374664010 = 61134864486695030790043729920 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (13, 1), (281, 1), (367, 1), (433, 1), (829, 1), (5790862669909049, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_281, prime_oneHundredSixtyFiveFG_367, prime_oneHundredSixtyFiveFG_433, prime_oneHundredSixtyFiveFG_829, prime_oneHundredSixtyFiveFG_5790862669909049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664011 : Nat.totient 195074035876965700539374664011 = 168391288724783857152345671680 := by
  rw [← show ((([(11, 1), (23, 1), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_23, prime_oneHundredSixtyFiveFG_137, prime_oneHundredSixtyFiveFG_1243169, prime_oneHundredSixtyFiveFG_4527184655447032079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664012 : Nat.totient 195074035876965700539374664012 = 65021781041829840026492601600 := by
  rw [← show ((([(2, 2), (3, 1), (22441, 1), (724395956348371658049161, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_22441, prime_oneHundredSixtyFiveFG_724395956348371658049161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664013 : Nat.totient 195074035876965700539374664013 = 195046949215041625761242781312 := by
  rw [← show ((([(7229, 1), (2251129, 1), (12924887, 1), (927457690639, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7229, prime_oneHundredSixtyFiveFG_2251129, prime_oneHundredSixtyFiveFG_12924887, prime_oneHundredSixtyFiveFG_927457690639]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664014 : Nat.totient 195074035876965700539374664014 = 97537007306462405025456291816 := by
  rw [← show ((([(2, 1), (9173893, 1), (10632020445244221866299, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_9173893, prime_oneHundredSixtyFiveFG_10632020445244221866299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664015 : Nat.totient 195074035876965700539374664015 = 104029049424960750993390673920 := by
  rw [← show ((([(3, 2), (5, 1), (18541, 1), (21617, 1), (8348687, 1), (1295508299753, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_18541, prime_oneHundredSixtyFiveFG_21617, prime_oneHundredSixtyFiveFG_8348687, prime_oneHundredSixtyFiveFG_1295508299753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664016 : Nat.totient 195074035876965700539374664016 = 97537017938482850269687332000 := by
  rw [← show ((([(2, 4), (12192127242310356283710916501, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_12192127242310356283710916501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664017 : Nat.totient 195074035876965700539374664017 = 166691871581313475852498707840 := by
  rw [← show ((([(7, 1), (457, 1), (1123, 1), (54300705579177180686021, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_457, prime_oneHundredSixtyFiveFG_1123, prime_oneHundredSixtyFiveFG_54300705579177180686021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664018 : Nat.totient 195074035876965700539374664018 = 62983545215881302416300323968 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (223, 1), (3940411987980561962981753, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_37, prime_oneHundredSixtyFiveFG_223, prime_oneHundredSixtyFiveFG_3940411987980561962981753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664019 : Nat.totient 195074035876965700539374664019 = 195074035876965700539374664018 := by
  rw [← show ((([(195074035876965700539374664019, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_195074035876965700539374664019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664020 : Nat.totient 195074035876965700539374664020 = 76007469459372337086230002560 := by
  rw [← show ((([(2, 2), (5, 1), (47, 1), (211, 1), (983533507497054051322853, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_47, prime_oneHundredSixtyFiveFG_211, prime_oneHundredSixtyFiveFG_983533507497054051322853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664021 : Nat.totient 195074035876965700539374664021 = 125936993550154168075297608576 := by
  rw [← show ((([(3, 1), (59, 1), (67, 1), (122791657, 1), (133962282976311967, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_59, prime_oneHundredSixtyFiveFG_67, prime_oneHundredSixtyFiveFG_122791657, prime_oneHundredSixtyFiveFG_133962282976311967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664022 : Nat.totient 195074035876965700539374664022 = 88670016307711682063352119900 := by
  rw [← show ((([(2, 1), (11, 2), (806091057342833473303201091, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_806091057342833473303201091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664023 : Nat.totient 195074035876965700539374664023 = 173802289544306488376106929280 := by
  rw [← show ((([(13, 1), (29, 1), (3061, 1), (169042064994073381940659, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_29, prime_oneHundredSixtyFiveFG_3061, prime_oneHundredSixtyFiveFG_169042064994073381940659]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664024 : Nat.totient 195074035876965700539374664024 = 52382895907663684881086349312 := by
  rw [← show ((([(2, 3), (3, 2), (7, 1), (17, 1), (709, 1), (95656009, 1), (335707867311353, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_709, prime_oneHundredSixtyFiveFG_95656009, prime_oneHundredSixtyFiveFG_335707867311353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664025 : Nat.totient 195074035876965700539374664025 = 152250120591167078257245696000 := by
  rw [← show ((([(5, 2), (41, 1), (67181, 1), (293269, 1), (9659685377123689, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_41, prime_oneHundredSixtyFiveFG_67181, prime_oneHundredSixtyFiveFG_293269, prime_oneHundredSixtyFiveFG_9659685377123689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664026 : Nat.totient 195074035876965700539374664026 = 96302301194849997324004611840 := by
  rw [← show ((([(2, 1), (79, 1), (1371913, 1), (128190281, 1), (7020381470099, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_79, prime_oneHundredSixtyFiveFG_1371913, prime_oneHundredSixtyFiveFG_128190281, prime_oneHundredSixtyFiveFG_7020381470099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664027 : Nat.totient 195074035876965700539374664027 = 128856243881198434784691780000 := by
  rw [← show ((([(3, 1), (109, 1), (154518491651, 1), (3860746233443951, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_109, prime_oneHundredSixtyFiveFG_154518491651, prime_oneHundredSixtyFiveFG_3860746233443951]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664028 : Nat.totient 195074035876965700539374664028 = 92377992401369720325545572224 := by
  rw [← show ((([(2, 2), (19, 1), (3863, 1), (58537, 1), (11350910713036676963, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_19, prime_oneHundredSixtyFiveFG_3863, prime_oneHundredSixtyFiveFG_58537, prime_oneHundredSixtyFiveFG_11350910713036676963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664029 : Nat.totient 195074035876965700539374664029 = 195035543160380080712949280704 := by
  rw [← show ((([(5387, 1), (85517, 1), (8256362479, 1), (51287471069, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5387, prime_oneHundredSixtyFiveFG_85517, prime_oneHundredSixtyFiveFG_8256362479, prime_oneHundredSixtyFiveFG_51287471069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664030 : Nat.totient 195074035876965700539374664030 = 51422566509003960098512260480 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (167, 1), (181, 1), (215121178501522590773563, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_167, prime_oneHundredSixtyFiveFG_181, prime_oneHundredSixtyFiveFG_215121178501522590773563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664031 : Nat.totient 195074035876965700539374664031 = 167206315020294739257240331104 := by
  rw [← show ((([(7, 1), (117717043, 1), (8765140303, 1), (27008670877, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_117717043, prime_oneHundredSixtyFiveFG_8765140303, prime_oneHundredSixtyFiveFG_27008670877]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664032 : Nat.totient 195074035876965700539374664032 = 97528994822752120414437512832 := by
  rw [← show ((([(2, 5), (12157, 1), (501444733170615953101543, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_12157, prime_oneHundredSixtyFiveFG_501444733170615953101543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664033 : Nat.totient 195074035876965700539374664033 = 118226493706465937299327456320 := by
  rw [← show ((([(3, 3), (11, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_607213, prime_oneHundredSixtyFiveFG_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664034 : Nat.totient 195074035876965700539374664034 = 93286093795071755644246224000 := by
  rw [← show ((([(2, 1), (23, 1), (9161, 1), (577088651, 1), (802151169023389, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_23, prime_oneHundredSixtyFiveFG_9161, prime_oneHundredSixtyFiveFG_577088651, prime_oneHundredSixtyFiveFG_802151169023389]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664035 : Nat.totient 195074035876965700539374664035 = 156059222436816431637374797824 := by
  rw [← show ((([(5, 1), (24910663, 1), (1566189032198506322689, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_24910663, prime_oneHundredSixtyFiveFG_1566189032198506322689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664036 : Nat.totient 195074035876965700539374664036 = 59742577169229639139983360000 := by
  rw [← show ((([(2, 2), (3, 1), (13, 1), (257, 1), (1291, 1), (351257, 1), (353501, 1), (30352877609, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_257, prime_oneHundredSixtyFiveFG_1291, prime_oneHundredSixtyFiveFG_351257, prime_oneHundredSixtyFiveFG_353501, prime_oneHundredSixtyFiveFG_30352877609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664037 : Nat.totient 195074035876965700539374664037 = 188781325000601967738588322080 := by
  rw [← show ((([(31, 1), (4535515513, 1), (1387430120502120979, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_31, prime_oneHundredSixtyFiveFG_4535515513, prime_oneHundredSixtyFiveFG_1387430120502120979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664038 : Nat.totient 195074035876965700539374664038 = 83603158183996659008388115776 := by
  rw [← show ((([(2, 1), (7, 1), (1706582509, 1), (8164773535422159913, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_1706582509, prime_oneHundredSixtyFiveFG_8164773535422159913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664039 : Nat.totient 195074035876965700539374664039 = 126053066155433713072983714816 := by
  rw [← show ((([(3, 1), (43, 1), (163, 1), (683, 1), (23017, 1), (55373, 1), (10657483763819, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_43, prime_oneHundredSixtyFiveFG_163, prime_oneHundredSixtyFiveFG_683, prime_oneHundredSixtyFiveFG_23017, prime_oneHundredSixtyFiveFG_55373, prime_oneHundredSixtyFiveFG_10657483763819]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664040 : Nat.totient 195074035876965700539374664040 = 77475411852425014235120167680 := by
  rw [← show ((([(2, 3), (5, 1), (197, 1), (491, 1), (50418713460813862866463, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_197, prime_oneHundredSixtyFiveFG_491, prime_oneHundredSixtyFiveFG_50418713460813862866463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664041 : Nat.totient 195074035876965700539374664041 = 183599092590063974336142102528 := by
  rw [← show ((([(17, 1), (8638877807737, 1), (1328290958879329, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_8638877807737, prime_oneHundredSixtyFiveFG_1328290958879329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664042 : Nat.totient 195074035876965700539374664042 = 64891157723261343803700272160 := by
  rw [← show ((([(2, 1), (3, 2), (487, 1), (37616242861, 1), (591592401373367, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_487, prime_oneHundredSixtyFiveFG_37616242861, prime_oneHundredSixtyFiveFG_591592401373367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664043 : Nat.totient 195074035876965700539374664043 = 195073844843435492431045053120 := by
  rw [← show ((([(1162991, 1), (8372717, 1), (20033494128790969, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_1162991, prime_oneHundredSixtyFiveFG_8372717, prime_oneHundredSixtyFiveFG_20033494128790969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664044 : Nat.totient 195074035876965700539374664044 = 85116941608650658282581824000 := by
  rw [← show ((([(2, 2), (11, 1), (53, 1), (71, 1), (131, 1), (8993759679696815118617, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_53, prime_oneHundredSixtyFiveFG_71, prime_oneHundredSixtyFiveFG_131, prime_oneHundredSixtyFiveFG_8993759679696815118617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664045 : Nat.totient 195074035876965700539374664045 = 89176702098760715497259815488 := by
  rw [← show ((([(3, 1), (5, 1), (7, 3), (5429792839, 1), (6982819718723939, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_5429792839, prime_oneHundredSixtyFiveFG_6982819718723939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664046 : Nat.totient 195074035876965700539374664046 = 96361873144001927431391632000 := by
  rw [← show ((([(2, 1), (83, 1), (2340099468701, 1), (502177283554481, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_83, prime_oneHundredSixtyFiveFG_2340099468701, prime_oneHundredSixtyFiveFG_502177283554481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664047 : Nat.totient 195074035876965700539374664047 = 184806981355189842673342712640 := by
  rw [← show ((([(19, 1), (95480042941, 1), (107530895500168793, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_19, prime_oneHundredSixtyFiveFG_95480042941, prime_oneHundredSixtyFiveFG_107530895500168793]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664048 : Nat.totient 195074035876965700539374664048 = 64108061064386282357633228800 := by
  rw [← show ((([(2, 4), (3, 1), (101, 1), (239, 1), (19577, 1), (405749, 1), (21195094540883, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_101, prime_oneHundredSixtyFiveFG_239, prime_oneHundredSixtyFiveFG_19577, prime_oneHundredSixtyFiveFG_405749, prime_oneHundredSixtyFiveFG_21195094540883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664049 : Nat.totient 195074035876965700539374664049 = 178859828455080580360314610176 := by
  rw [← show ((([(13, 1), (149, 1), (100709362868851678130807777, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_149, prime_oneHundredSixtyFiveFG_100709362868851678130807777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664050 : Nat.totient 195074035876965700539374664050 = 78024199763710380813888794000 := by
  rw [← show ((([(2, 1), (5, 2), (14411, 1), (270729353794970093039171, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_14411, prime_oneHundredSixtyFiveFG_270729353794970093039171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664051 : Nat.totient 195074035876965700539374664051 = 130049357245561893505524409440 := by
  rw [← show ((([(3, 2), (22622892419, 1), (958095564164668681, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_22622892419, prime_oneHundredSixtyFiveFG_958095564164668681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664052 : Nat.totient 195074035876965700539374664052 = 79863965551861890735624228864 := by
  rw [← show ((([(2, 2), (7, 1), (29, 1), (97, 1), (3323, 1), (687023, 1), (1084850985537467, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_29, prime_oneHundredSixtyFiveFG_97, prime_oneHundredSixtyFiveFG_3323, prime_oneHundredSixtyFiveFG_687023, prime_oneHundredSixtyFiveFG_1084850985537467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664053 : Nat.totient 195074035876965700539374664053 = 195074012068519271325479564800 := by
  rw [← show ((([(8199473, 1), (11270457881, 1), (2110920943181, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_8199473, prime_oneHundredSixtyFiveFG_11270457881, prime_oneHundredSixtyFiveFG_2110920943181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664054 : Nat.totient 195074035876965700539374664054 = 64281018608631894271447872000 := by
  rw [← show ((([(2, 1), (3, 1), (89, 1), (4931, 1), (9312211, 1), (7955553520153241, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_89, prime_oneHundredSixtyFiveFG_4931, prime_oneHundredSixtyFiveFG_9312211, prime_oneHundredSixtyFiveFG_7955553520153241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664055 : Nat.totient 195074035876965700539374664055 = 138033219461306834335043589120 := by
  rw [← show ((([(5, 1), (11, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_37, prime_oneHundredSixtyFiveFG_31177, prime_oneHundredSixtyFiveFG_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664056 : Nat.totient 195074035876965700539374664056 = 97489790665160805603364619520 := by
  rw [← show ((([(2, 3), (2371, 1), (16187, 1), (1462199, 1), (434515305643609, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_2371, prime_oneHundredSixtyFiveFG_16187, prime_oneHundredSixtyFiveFG_1462199, prime_oneHundredSixtyFiveFG_434515305643609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664057 : Nat.totient 195074035876965700539374664057 = 124150177645402764629578970880 := by
  rw [← show ((([(3, 1), (23, 2), (509, 1), (264889, 1), (911676659536508311, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_23, prime_oneHundredSixtyFiveFG_509, prime_oneHundredSixtyFiveFG_264889, prime_oneHundredSixtyFiveFG_911676659536508311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664058 : Nat.totient 195074035876965700539374664058 = 91688003626929078502983985920 := by
  rw [← show ((([(2, 1), (17, 1), (823, 1), (1084769671, 1), (6426628307172589, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_823, prime_oneHundredSixtyFiveFG_1084769671, prime_oneHundredSixtyFiveFG_6426628307172589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664059 : Nat.totient 195074035876965700539374664059 = 167100690088696184053050376608 := by
  rw [← show ((([(7, 1), (1583, 1), (1107895133, 1), (15889925454288383, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_1583, prime_oneHundredSixtyFiveFG_1107895133, prime_oneHundredSixtyFiveFG_15889925454288383]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664060 : Nat.totient 195074035876965700539374664060 = 51533575880619876138889678080 := by
  rw [← show ((([(2, 2), (3, 3), (5, 1), (107, 1), (43001837, 1), (78511797954027271, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_107, prime_oneHundredSixtyFiveFG_43001837, prime_oneHundredSixtyFiveFG_78511797954027271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664061 : Nat.totient 195074035876965700539374664061 = 194633612714287022081162673840 := by
  rw [← show ((([(467, 1), (8573, 1), (48724766310286365550171, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_467, prime_oneHundredSixtyFiveFG_8573, prime_oneHundredSixtyFiveFG_48724766310286365550171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664062 : Nat.totient 195074035876965700539374664062 = 90031475819699536381577284512 := by
  rw [← show ((([(2, 1), (13, 1), (33413, 1), (224548754488655613705599, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_33413, prime_oneHundredSixtyFiveFG_224548754488655613705599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664063 : Nat.totient 195074035876965700539374664063 = 129747425144558569554617934720 := by
  rw [← show ((([(3, 1), (431, 1), (670673, 1), (224952136074415902667, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_431, prime_oneHundredSixtyFiveFG_670673, prime_oneHundredSixtyFiveFG_224952136074415902667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664064 : Nat.totient 195074035876965700539374664064 = 97252897019692037239258585600 := by
  rw [← show ((([(2, 7), (347, 1), (32051, 1), (137030878047549266579, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_347, prime_oneHundredSixtyFiveFG_32051, prime_oneHundredSixtyFiveFG_137030878047549266579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664065 : Nat.totient 195074035876965700539374664065 = 155846323887454477560624307200 := by
  rw [← show ((([(5, 1), (733, 1), (2786044081081, 1), (19104580532281, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_733, prime_oneHundredSixtyFiveFG_2786044081081, prime_oneHundredSixtyFiveFG_19104580532281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664066 : Nat.totient 195074035876965700539374664066 = 46713071663293406800497868800 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (11, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_19, prime_oneHundredSixtyFiveFG_41, prime_oneHundredSixtyFiveFG_397, prime_oneHundredSixtyFiveFG_13617913, prime_oneHundredSixtyFiveFG_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664067 : Nat.totient 195074035876965700539374664067 = 185203231478682881947185484800 := by
  rw [← show ((([(47, 1), (61, 1), (73, 1), (10357, 1), (89994286861309679141, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_47, prime_oneHundredSixtyFiveFG_61, prime_oneHundredSixtyFiveFG_73, prime_oneHundredSixtyFiveFG_10357, prime_oneHundredSixtyFiveFG_89994286861309679141]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664068 : Nat.totient 195074035876965700539374664068 = 94291616705245581142817876160 := by
  rw [← show ((([(2, 2), (31, 1), (953, 1), (1650763597780910034012919, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_31, prime_oneHundredSixtyFiveFG_953, prime_oneHundredSixtyFiveFG_1650763597780910034012919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664069 : Nat.totient 195074035876965700539374664069 = 130049305079246007104861568000 := by
  rw [← show ((([(3, 2), (2492701, 1), (8695344076653562208641, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_2492701, prime_oneHundredSixtyFiveFG_8695344076653562208641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664070 : Nat.totient 195074035876965700539374664070 = 77899347881704414463060158080 := by
  rw [← show ((([(2, 1), (5, 1), (599, 1), (74166855821, 1), (439099334161333, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_599, prime_oneHundredSixtyFiveFG_74166855821, prime_oneHundredSixtyFiveFG_439099334161333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664071 : Nat.totient 195074035876965700539374664071 = 195074034545209175441746339000 := by
  rw [← show ((([(169336931, 1), (1086248831, 1), (1060519021811, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_169336931, prime_oneHundredSixtyFiveFG_1086248831, prime_oneHundredSixtyFiveFG_1060519021811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664072 : Nat.totient 195074035876965700539374664072 = 65024638618371364261909499520 := by
  rw [← show ((([(2, 3), (3, 1), (1625321, 1), (5000910483656400298243, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_1625321, prime_oneHundredSixtyFiveFG_5000910483656400298243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664073 : Nat.totient 195074035876965700539374664073 = 167206316465970600462321140628 := by
  rw [← show ((([(7, 1), (27867719410995100077053523439, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_27867719410995100077053523439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664074 : Nat.totient 195074035876965700539374664074 = 97537017938482850269687332036 := by
  rw [← show ((([(2, 1), (97537017938482850269687332037, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_97537017938482850269687332037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664075 : Nat.totient 195074035876965700539374664075 = 90375338423598661376393472000 := by
  rw [← show ((([(3, 1), (5, 2), (13, 1), (17, 1), (7591, 1), (1550411355806685423811, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_7591, prime_oneHundredSixtyFiveFG_1550411355806685423811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664076 : Nat.totient 195074035876965700539374664076 = 97536696827694941268081655872 := by
  rw [← show ((([(2, 2), (336827, 1), (3092989, 1), (46811677584201773, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_336827, prime_oneHundredSixtyFiveFG_3092989, prime_oneHundredSixtyFiveFG_46811677584201773]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664077 : Nat.totient 195074035876965700539374664077 = 177184321192355660086696512000 := by
  rw [← show ((([(11, 1), (1697, 1), (3461, 1), (3019418713742564280571, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_1697, prime_oneHundredSixtyFiveFG_3461, prime_oneHundredSixtyFiveFG_3019418713742564280571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664078 : Nat.totient 195074035876965700539374664078 = 65024645819768589229586035200 := by
  rw [← show ((([(2, 1), (3, 2), (3148051, 1), (5351669, 1), (643273943197409, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_3148051, prime_oneHundredSixtyFiveFG_5351669, prime_oneHundredSixtyFiveFG_643273943197409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664079 : Nat.totient 195074035876965700539374664079 = 195049472078865019531012326144 := by
  rw [← show ((([(7949, 1), (10916527, 1), (37322557, 1), (60232527689, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7949, prime_oneHundredSixtyFiveFG_10916527, prime_oneHundredSixtyFiveFG_37322557, prime_oneHundredSixtyFiveFG_60232527689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664080 : Nat.totient 195074035876965700539374664080 = 62890275497937405000900544512 := by
  rw [← show ((([(2, 4), (5, 1), (7, 1), (23, 1), (59, 1), (1160644117, 1), (221173209466147, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_23, prime_oneHundredSixtyFiveFG_59, prime_oneHundredSixtyFiveFG_1160644117, prime_oneHundredSixtyFiveFG_221173209466147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664081 : Nat.totient 195074035876965700539374664081 = 124733341049441416193251660800 := by
  rw [← show ((([(3, 1), (29, 1), (151, 1), (14849207267790644784910913, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_29, prime_oneHundredSixtyFiveFG_151, prime_oneHundredSixtyFiveFG_14849207267790644784910913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664082 : Nat.totient 195074035876965700539374664082 = 94926541321165280642082373248 := by
  rw [← show ((([(2, 1), (43, 1), (359, 1), (1237, 1), (5107835118109486565689, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_43, prime_oneHundredSixtyFiveFG_359, prime_oneHundredSixtyFiveFG_1237, prime_oneHundredSixtyFiveFG_5107835118109486565689]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664083 : Nat.totient 195074035876965700539374664083 = 195067863891366376669638870528 := by
  rw [← show ((([(32083, 1), (2127409, 1), (2858074240329689489, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_32083, prime_oneHundredSixtyFiveFG_2127409, prime_oneHundredSixtyFiveFG_2858074240329689489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664084 : Nat.totient 195074035876965700539374664084 = 65024662118540335432341120000 := by
  rw [← show ((([(2, 2), (3, 1), (4015201, 1), (208088557, 1), (19456411085651, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_4015201, prime_oneHundredSixtyFiveFG_208088557, prime_oneHundredSixtyFiveFG_19456411085651]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664085 : Nat.totient 195074035876965700539374664085 = 146675190747783170470822316352 := by
  rw [← show ((([(5, 1), (19, 1), (127, 1), (23447, 1), (689580321364101784147, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_19, prime_oneHundredSixtyFiveFG_127, prime_oneHundredSixtyFiveFG_23447, prime_oneHundredSixtyFiveFG_689580321364101784147]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664086 : Nat.totient 195074035876965700539374664086 = 97202777609381770305314818560 := by
  rw [← show ((([(2, 1), (613, 1), (661, 1), (4909, 1), (12763, 1), (253247, 1), (15171112499, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_613, prime_oneHundredSixtyFiveFG_661, prime_oneHundredSixtyFiveFG_4909, prime_oneHundredSixtyFiveFG_12763, prime_oneHundredSixtyFiveFG_253247, prime_oneHundredSixtyFiveFG_15171112499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664087 : Nat.totient 195074035876965700539374664087 = 111470877643980400308214093440 := by
  rw [← show ((([(3, 4), (7, 1), (344045918654260494778438561, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_344045918654260494778438561]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664088 : Nat.totient 195074035876965700539374664088 = 80601326531631549668232552960 := by
  rw [← show ((([(2, 3), (11, 1), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_67, prime_oneHundredSixtyFiveFG_3067, prime_oneHundredSixtyFiveFG_829821849978416232493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664089 : Nat.totient 195074035876965700539374664089 = 195069233695919665102956677520 := by
  rw [← show ((([(66877, 1), (103471, 1), (28190581847848388867, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_66877, prime_oneHundredSixtyFiveFG_103471, prime_oneHundredSixtyFiveFG_28190581847848388867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664090 : Nat.totient 195074035876965700539374664090 = 52019742900524186810499910416 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (6502467862565523351312488803, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_6502467862565523351312488803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664091 : Nat.totient 195074035876965700539374664091 = 193899016404703266142012047360 := by
  rw [← show ((([(311, 1), (557, 1), (977, 1), (23740417, 1), (48551312878337, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_311, prime_oneHundredSixtyFiveFG_557, prime_oneHundredSixtyFiveFG_977, prime_oneHundredSixtyFiveFG_23740417, prime_oneHundredSixtyFiveFG_48551312878337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664092 : Nat.totient 195074035876965700539374664092 = 89317223865996881819863191552 := by
  rw [← show ((([(2, 2), (17, 1), (37, 1), (71249, 1), (1088203351443940163963, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_17, prime_oneHundredSixtyFiveFG_37, prime_oneHundredSixtyFiveFG_71249, prime_oneHundredSixtyFiveFG_1088203351443940163963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664093 : Nat.totient 195074035876965700539374664093 = 129635324188373660850812488320 := by
  rw [← show ((([(3, 1), (571, 1), (857, 1), (3727, 1), (35653477162396384699, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_571, prime_oneHundredSixtyFiveFG_857, prime_oneHundredSixtyFiveFG_3727, prime_oneHundredSixtyFiveFG_35653477162396384699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664094 : Nat.totient 195074035876965700539374664094 = 83603158232985300231160570284 := by
  rw [← show ((([(2, 1), (7, 2), (1990551386499650005503823103, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_1990551386499650005503823103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664095 : Nat.totient 195074035876965700539374664095 = 155997569583160244129472261760 := by
  rw [← show ((([(5, 1), (2531, 1), (15414779603079075506864849, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_2531, prime_oneHundredSixtyFiveFG_15414779603079075506864849]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664096 : Nat.totient 195074035876965700539374664096 = 65024652029595999305164822656 := by
  rw [← show ((([(2, 5), (3, 2), (2444899, 1), (277042283689663805783, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_2444899, prime_oneHundredSixtyFiveFG_277042283689663805783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664097 : Nat.totient 195074035876965700539374664097 = 191393086106330728263121828272 := by
  rw [← show ((([(53, 1), (622247, 1), (5915082252478265715067, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_53, prime_oneHundredSixtyFiveFG_622247, prime_oneHundredSixtyFiveFG_5915082252478265715067]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664098 : Nat.totient 195074035876965700539374664098 = 96587174313726994613187166464 := by
  rw [← show ((([(2, 1), (103, 2), (52543, 1), (101653, 1), (1030297, 1), (1670696347, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_103, prime_oneHundredSixtyFiveFG_52543, prime_oneHundredSixtyFiveFG_101653, prime_oneHundredSixtyFiveFG_1030297, prime_oneHundredSixtyFiveFG_1670696347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664099 : Nat.totient 195074035876965700539374664099 = 114412892477896108097440588800 := by
  rw [← show ((([(3, 1), (11, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_3, prime_oneHundredSixtyFiveFG_11, prime_oneHundredSixtyFiveFG_31, prime_oneHundredSixtyFiveFG_3599009, prime_oneHundredSixtyFiveFG_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664100 : Nat.totient 195074035876965700539374664100 = 77968013017928937051762432000 := by
  rw [← show ((([(2, 2), (5, 2), (1873, 1), (3911, 1), (180272117, 1), (1477220469691, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_2, prime_oneHundredSixtyFiveFG_5, prime_oneHundredSixtyFiveFG_1873, prime_oneHundredSixtyFiveFG_3911, prime_oneHundredSixtyFiveFG_180272117, prime_oneHundredSixtyFiveFG_1477220469691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSixtyFiveFG_195074035876965700539374664101 : Nat.totient 195074035876965700539374664101 = 153859830920246605981670148096 := by
  rw [← show ((([(7, 1), (13, 1), (353, 1), (3259, 1), (31697357779, 1), (58786275967, 1)] : List FactorBlock).map factorBlockValue).prod) = 195074035876965700539374664101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSixtyFiveFG_7, prime_oneHundredSixtyFiveFG_13, prime_oneHundredSixtyFiveFG_353, prime_oneHundredSixtyFiveFG_3259, prime_oneHundredSixtyFiveFG_31697357779, prime_oneHundredSixtyFiveFG_58786275967]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSixtyFiveFG : certifiedKill 1 195074035876965700539374663999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664000, phi_oneHundredSixtyFiveFG_195074035876965700539374664001, phi_oneHundredSixtyFiveFG_195074035876965700539374664002,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664003, phi_oneHundredSixtyFiveFG_195074035876965700539374664004, phi_oneHundredSixtyFiveFG_195074035876965700539374664005,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664006, phi_oneHundredSixtyFiveFG_195074035876965700539374664007, phi_oneHundredSixtyFiveFG_195074035876965700539374664008,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664009, phi_oneHundredSixtyFiveFG_195074035876965700539374664010, phi_oneHundredSixtyFiveFG_195074035876965700539374664011,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664012, phi_oneHundredSixtyFiveFG_195074035876965700539374664013, phi_oneHundredSixtyFiveFG_195074035876965700539374664014,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664015, phi_oneHundredSixtyFiveFG_195074035876965700539374664016, phi_oneHundredSixtyFiveFG_195074035876965700539374664017,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664018, phi_oneHundredSixtyFiveFG_195074035876965700539374664019, phi_oneHundredSixtyFiveFG_195074035876965700539374664020,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664021, phi_oneHundredSixtyFiveFG_195074035876965700539374664022, phi_oneHundredSixtyFiveFG_195074035876965700539374664023,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664024, phi_oneHundredSixtyFiveFG_195074035876965700539374664025, phi_oneHundredSixtyFiveFG_195074035876965700539374664026,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664027, phi_oneHundredSixtyFiveFG_195074035876965700539374664028, phi_oneHundredSixtyFiveFG_195074035876965700539374664029,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664030, phi_oneHundredSixtyFiveFG_195074035876965700539374664031, phi_oneHundredSixtyFiveFG_195074035876965700539374664032,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664033, phi_oneHundredSixtyFiveFG_195074035876965700539374664034, phi_oneHundredSixtyFiveFG_195074035876965700539374664035,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664036, phi_oneHundredSixtyFiveFG_195074035876965700539374664037, phi_oneHundredSixtyFiveFG_195074035876965700539374664038,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664039, phi_oneHundredSixtyFiveFG_195074035876965700539374664040, phi_oneHundredSixtyFiveFG_195074035876965700539374664041,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664042, phi_oneHundredSixtyFiveFG_195074035876965700539374664043, phi_oneHundredSixtyFiveFG_195074035876965700539374664044,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664045, phi_oneHundredSixtyFiveFG_195074035876965700539374664046, phi_oneHundredSixtyFiveFG_195074035876965700539374664047,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664048, phi_oneHundredSixtyFiveFG_195074035876965700539374664049, phi_oneHundredSixtyFiveFG_195074035876965700539374664050,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664051, phi_oneHundredSixtyFiveFG_195074035876965700539374664052, phi_oneHundredSixtyFiveFG_195074035876965700539374664053,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664054, phi_oneHundredSixtyFiveFG_195074035876965700539374664055, phi_oneHundredSixtyFiveFG_195074035876965700539374664056,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664057, phi_oneHundredSixtyFiveFG_195074035876965700539374664058, phi_oneHundredSixtyFiveFG_195074035876965700539374664059,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664060, phi_oneHundredSixtyFiveFG_195074035876965700539374664061, phi_oneHundredSixtyFiveFG_195074035876965700539374664062,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664063, phi_oneHundredSixtyFiveFG_195074035876965700539374664064, phi_oneHundredSixtyFiveFG_195074035876965700539374664065,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664066, phi_oneHundredSixtyFiveFG_195074035876965700539374664067, phi_oneHundredSixtyFiveFG_195074035876965700539374664068,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664069, phi_oneHundredSixtyFiveFG_195074035876965700539374664070, phi_oneHundredSixtyFiveFG_195074035876965700539374664071,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664072, phi_oneHundredSixtyFiveFG_195074035876965700539374664073, phi_oneHundredSixtyFiveFG_195074035876965700539374664074,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664075, phi_oneHundredSixtyFiveFG_195074035876965700539374664076, phi_oneHundredSixtyFiveFG_195074035876965700539374664077,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664078, phi_oneHundredSixtyFiveFG_195074035876965700539374664079, phi_oneHundredSixtyFiveFG_195074035876965700539374664080,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664081, phi_oneHundredSixtyFiveFG_195074035876965700539374664082, phi_oneHundredSixtyFiveFG_195074035876965700539374664083,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664084, phi_oneHundredSixtyFiveFG_195074035876965700539374664085, phi_oneHundredSixtyFiveFG_195074035876965700539374664086,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664087, phi_oneHundredSixtyFiveFG_195074035876965700539374664088, phi_oneHundredSixtyFiveFG_195074035876965700539374664089,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664090, phi_oneHundredSixtyFiveFG_195074035876965700539374664091, phi_oneHundredSixtyFiveFG_195074035876965700539374664092,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664093, phi_oneHundredSixtyFiveFG_195074035876965700539374664094, phi_oneHundredSixtyFiveFG_195074035876965700539374664095,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664096, phi_oneHundredSixtyFiveFG_195074035876965700539374664097, phi_oneHundredSixtyFiveFG_195074035876965700539374664098,
    phi_oneHundredSixtyFiveFG_195074035876965700539374664099, phi_oneHundredSixtyFiveFG_195074035876965700539374664100, phi_oneHundredSixtyFiveFG_195074035876965700539374664101]

end TotientTailPeriodKiller
end Erdos249257
