import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredSevenDAFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredSevenDAFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredSevenDAFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredSevenDAFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredSevenDAFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredSevenDAFastPow a n * oneHundredSevenDAFastPow a n * a else oneHundredSevenDAFastPow a n * oneHundredSevenDAFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredSevenDA_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredSevenDA_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredSevenDA_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredSevenDA_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredSevenDA_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredSevenDA_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredSevenDA_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredSevenDA_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredSevenDA_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredSevenDA_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredSevenDA_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredSevenDA_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredSevenDA_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredSevenDA_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredSevenDA_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredSevenDA_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredSevenDA_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredSevenDA_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredSevenDA_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredSevenDA_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredSevenDA_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredSevenDA_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredSevenDA_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredSevenDA_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredSevenDA_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredSevenDA_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredSevenDA_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredSevenDA_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredSevenDA_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredSevenDA_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredSevenDA_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredSevenDA_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredSevenDA_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredSevenDA_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredSevenDA_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredSevenDA_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredSevenDA_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredSevenDA_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredSevenDA_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredSevenDA_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredSevenDA_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredSevenDA_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredSevenDA_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredSevenDA_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredSevenDA_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredSevenDA_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredSevenDA_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredSevenDA_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredSevenDA_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredSevenDA_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredSevenDA_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredSevenDA_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredSevenDA_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredSevenDA_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredSevenDA_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredSevenDA_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredSevenDA_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredSevenDA_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredSevenDA_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredSevenDA_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredSevenDA_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredSevenDA_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredSevenDA_331 : Nat.Prime 331 := by norm_num

private theorem prime_oneHundredSevenDA_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredSevenDA_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredSevenDA_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredSevenDA_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredSevenDA_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredSevenDA_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredSevenDA_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredSevenDA_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredSevenDA_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredSevenDA_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredSevenDA_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredSevenDA_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredSevenDA_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredSevenDA_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredSevenDA_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredSevenDA_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredSevenDA_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredSevenDA_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredSevenDA_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredSevenDA_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredSevenDA_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredSevenDA_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredSevenDA_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredSevenDA_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredSevenDA_607 : Nat.Prime 607 := by norm_num

private theorem prime_oneHundredSevenDA_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredSevenDA_647 : Nat.Prime 647 := by norm_num

private theorem prime_oneHundredSevenDA_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredSevenDA_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredSevenDA_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredSevenDA_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredSevenDA_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredSevenDA_727 : Nat.Prime 727 := by norm_num

private theorem prime_oneHundredSevenDA_733 : Nat.Prime 733 := by norm_num

private theorem prime_oneHundredSevenDA_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredSevenDA_757 : Nat.Prime 757 := by norm_num

private theorem prime_oneHundredSevenDA_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredSevenDA_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredSevenDA_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredSevenDA_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredSevenDA_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredSevenDA_877 : Nat.Prime 877 := by norm_num

private theorem prime_oneHundredSevenDA_907 : Nat.Prime 907 := by norm_num

private theorem prime_oneHundredSevenDA_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredSevenDA_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredSevenDA_983 : Nat.Prime 983 := by norm_num

private theorem prime_oneHundredSevenDA_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredSevenDA_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredSevenDA_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredSevenDA_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredSevenDA_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredSevenDA_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredSevenDA_1091 : Nat.Prime 1091 := by norm_num

private theorem prime_oneHundredSevenDA_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredSevenDA_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredSevenDA_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredSevenDA_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredSevenDA_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredSevenDA_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredSevenDA_1249 : Nat.Prime 1249 := by norm_num

private theorem prime_oneHundredSevenDA_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredSevenDA_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredSevenDA_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredSevenDA_1361 : Nat.Prime 1361 := by norm_num

private theorem prime_oneHundredSevenDA_1423 : Nat.Prime 1423 := by norm_num

private theorem prime_oneHundredSevenDA_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredSevenDA_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredSevenDA_1471 : Nat.Prime 1471 := by norm_num

private theorem prime_oneHundredSevenDA_1481 : Nat.Prime 1481 := by norm_num

private theorem prime_oneHundredSevenDA_1483 : Nat.Prime 1483 := by norm_num

private theorem prime_oneHundredSevenDA_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredSevenDA_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredSevenDA_1579 : Nat.Prime 1579 := by norm_num

private theorem prime_oneHundredSevenDA_1621 : Nat.Prime 1621 := by norm_num

private theorem prime_oneHundredSevenDA_1627 : Nat.Prime 1627 := by norm_num

private theorem prime_oneHundredSevenDA_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredSevenDA_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredSevenDA_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredSevenDA_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredSevenDA_1733 : Nat.Prime 1733 := by norm_num

private theorem prime_oneHundredSevenDA_1783 : Nat.Prime 1783 := by norm_num

private theorem prime_oneHundredSevenDA_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredSevenDA_1877 : Nat.Prime 1877 := by norm_num

private theorem prime_oneHundredSevenDA_2017 : Nat.Prime 2017 := by norm_num

private theorem prime_oneHundredSevenDA_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredSevenDA_2099 : Nat.Prime 2099 := by norm_num

private theorem prime_oneHundredSevenDA_2143 : Nat.Prime 2143 := by norm_num

private theorem prime_oneHundredSevenDA_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredSevenDA_2239 : Nat.Prime 2239 := by norm_num

private theorem prime_oneHundredSevenDA_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredSevenDA_2287 : Nat.Prime 2287 := by norm_num

private theorem prime_oneHundredSevenDA_2351 : Nat.Prime 2351 := by norm_num

private theorem prime_oneHundredSevenDA_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredSevenDA_2389 : Nat.Prime 2389 := by norm_num

private theorem prime_oneHundredSevenDA_2399 : Nat.Prime 2399 := by norm_num

private theorem prime_oneHundredSevenDA_2441 : Nat.Prime 2441 := by norm_num

private theorem prime_oneHundredSevenDA_2521 : Nat.Prime 2521 := by norm_num

private theorem prime_oneHundredSevenDA_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredSevenDA_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredSevenDA_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredSevenDA_2741 : Nat.Prime 2741 := by norm_num

private theorem prime_oneHundredSevenDA_2789 : Nat.Prime 2789 := by norm_num

private theorem prime_oneHundredSevenDA_2791 : Nat.Prime 2791 := by norm_num

private theorem prime_oneHundredSevenDA_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredSevenDA_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredSevenDA_2957 : Nat.Prime 2957 := by norm_num

private theorem prime_oneHundredSevenDA_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredSevenDA_3089 : Nat.Prime 3089 := by norm_num

private theorem prime_oneHundredSevenDA_3251 : Nat.Prime 3251 := by norm_num

private theorem prime_oneHundredSevenDA_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredSevenDA_3323 : Nat.Prime 3323 := by norm_num

private theorem prime_oneHundredSevenDA_3359 : Nat.Prime 3359 := by norm_num

private theorem prime_oneHundredSevenDA_3559 : Nat.Prime 3559 := by norm_num

private theorem prime_oneHundredSevenDA_3607 : Nat.Prime 3607 := by norm_num

private theorem prime_oneHundredSevenDA_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredSevenDA_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredSevenDA_3761 : Nat.Prime 3761 := by norm_num

private theorem prime_oneHundredSevenDA_4057 : Nat.Prime 4057 := by norm_num

private theorem prime_oneHundredSevenDA_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredSevenDA_4211 : Nat.Prime 4211 := by norm_num

private theorem prime_oneHundredSevenDA_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredSevenDA_4373 : Nat.Prime 4373 := by norm_num

private theorem prime_oneHundredSevenDA_5011 : Nat.Prime 5011 := by norm_num

private theorem prime_oneHundredSevenDA_5039 : Nat.Prime 5039 := by norm_num

private theorem prime_oneHundredSevenDA_5077 : Nat.Prime 5077 := by norm_num

private theorem prime_oneHundredSevenDA_5107 : Nat.Prime 5107 := by norm_num

private theorem prime_oneHundredSevenDA_5197 : Nat.Prime 5197 := by norm_num

private theorem prime_oneHundredSevenDA_5303 : Nat.Prime 5303 := by norm_num

private theorem prime_oneHundredSevenDA_5431 : Nat.Prime 5431 := by norm_num

private theorem prime_oneHundredSevenDA_5503 : Nat.Prime 5503 := by norm_num

private theorem prime_oneHundredSevenDA_5653 : Nat.Prime 5653 := by norm_num

private theorem prime_oneHundredSevenDA_5701 : Nat.Prime 5701 := by norm_num

private theorem prime_oneHundredSevenDA_5737 : Nat.Prime 5737 := by norm_num

private theorem prime_oneHundredSevenDA_5741 : Nat.Prime 5741 := by norm_num

private theorem prime_oneHundredSevenDA_5807 : Nat.Prime 5807 := by norm_num

private theorem prime_oneHundredSevenDA_5849 : Nat.Prime 5849 := by norm_num

private theorem prime_oneHundredSevenDA_5881 : Nat.Prime 5881 := by norm_num

private theorem prime_oneHundredSevenDA_5903 : Nat.Prime 5903 := by norm_num

private theorem prime_oneHundredSevenDA_6301 : Nat.Prime 6301 := by norm_num

private theorem prime_oneHundredSevenDA_6397 : Nat.Prime 6397 := by norm_num

private theorem prime_oneHundredSevenDA_7127 : Nat.Prime 7127 := by norm_num

private theorem prime_oneHundredSevenDA_7193 : Nat.Prime 7193 := by norm_num

private theorem prime_oneHundredSevenDA_7529 : Nat.Prime 7529 := by norm_num

private theorem prime_oneHundredSevenDA_7901 : Nat.Prime 7901 := by norm_num

private theorem prime_oneHundredSevenDA_7919 : Nat.Prime 7919 := by norm_num

private theorem prime_oneHundredSevenDA_8369 : Nat.Prime 8369 := by norm_num

private theorem prime_oneHundredSevenDA_9103 : Nat.Prime 9103 := by norm_num

private theorem prime_oneHundredSevenDA_9181 : Nat.Prime 9181 := by norm_num

private theorem prime_oneHundredSevenDA_9839 : Nat.Prime 9839 := by norm_num

private theorem prime_oneHundredSevenDA_9967 : Nat.Prime 9967 := by norm_num

private theorem prime_oneHundredSevenDA_10037 : Nat.Prime 10037 := by norm_num

private theorem prime_oneHundredSevenDA_10039 : Nat.Prime 10039 := by norm_num

private theorem prime_oneHundredSevenDA_10103 : Nat.Prime 10103 := by norm_num

private theorem prime_oneHundredSevenDA_10333 : Nat.Prime 10333 := by norm_num

private theorem prime_oneHundredSevenDA_10457 : Nat.Prime 10457 := by norm_num

private theorem prime_oneHundredSevenDA_10939 : Nat.Prime 10939 := by norm_num

private theorem prime_oneHundredSevenDA_11579 : Nat.Prime 11579 := by norm_num

private theorem prime_oneHundredSevenDA_11783 : Nat.Prime 11783 := by norm_num

private theorem prime_oneHundredSevenDA_11903 : Nat.Prime 11903 := by norm_num

private theorem prime_oneHundredSevenDA_11969 : Nat.Prime 11969 := by norm_num

private theorem prime_oneHundredSevenDA_12107 : Nat.Prime 12107 := by norm_num

private theorem prime_oneHundredSevenDA_12253 : Nat.Prime 12253 := by norm_num

private theorem prime_oneHundredSevenDA_12289 : Nat.Prime 12289 := by norm_num

private theorem prime_oneHundredSevenDA_13967 : Nat.Prime 13967 := by norm_num

private theorem prime_oneHundredSevenDA_14341 : Nat.Prime 14341 := by norm_num

private theorem prime_oneHundredSevenDA_15013 : Nat.Prime 15013 := by norm_num

private theorem prime_oneHundredSevenDA_15569 : Nat.Prime 15569 := by norm_num

private theorem prime_oneHundredSevenDA_15937 : Nat.Prime 15937 := by norm_num

private theorem prime_oneHundredSevenDA_16333 : Nat.Prime 16333 := by norm_num

private theorem prime_oneHundredSevenDA_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredSevenDA_16381 : Nat.Prime 16381 := by norm_num

private theorem prime_oneHundredSevenDA_16831 : Nat.Prime 16831 := by norm_num

private theorem prime_oneHundredSevenDA_16883 : Nat.Prime 16883 := by norm_num

private theorem prime_oneHundredSevenDA_16903 : Nat.Prime 16903 := by norm_num

private theorem prime_oneHundredSevenDA_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredSevenDA_17393 : Nat.Prime 17393 := by norm_num

private theorem prime_oneHundredSevenDA_17669 : Nat.Prime 17669 := by norm_num

private theorem prime_oneHundredSevenDA_17783 : Nat.Prime 17783 := by norm_num

private theorem prime_oneHundredSevenDA_17881 : Nat.Prime 17881 := by norm_num

private theorem prime_oneHundredSevenDA_18899 : Nat.Prime 18899 := by norm_num

private theorem prime_oneHundredSevenDA_18917 : Nat.Prime 18917 := by norm_num

private theorem prime_oneHundredSevenDA_19309 : Nat.Prime 19309 := by norm_num

private theorem prime_oneHundredSevenDA_20483 : Nat.Prime 20483 := by norm_num

private theorem prime_oneHundredSevenDA_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredSevenDA_21211 : Nat.Prime 21211 := by norm_num

private theorem prime_oneHundredSevenDA_22571 : Nat.Prime 22571 := by norm_num

private theorem prime_oneHundredSevenDA_22573 : Nat.Prime 22573 := by norm_num

private theorem prime_oneHundredSevenDA_23633 : Nat.Prime 23633 := by norm_num

private theorem prime_oneHundredSevenDA_23671 : Nat.Prime 23671 := by norm_num

private theorem prime_oneHundredSevenDA_24547 : Nat.Prime 24547 := by norm_num

private theorem prime_oneHundredSevenDA_25301 : Nat.Prime 25301 := by norm_num

private theorem prime_oneHundredSevenDA_25373 : Nat.Prime 25373 := by norm_num

private theorem prime_oneHundredSevenDA_25621 : Nat.Prime 25621 := by norm_num

private theorem prime_oneHundredSevenDA_25997 : Nat.Prime 25997 := by norm_num

private theorem prime_oneHundredSevenDA_26723 : Nat.Prime 26723 := by norm_num

private theorem prime_oneHundredSevenDA_28579 : Nat.Prime 28579 := by norm_num

private theorem prime_oneHundredSevenDA_29147 : Nat.Prime 29147 := by norm_num

private theorem prime_oneHundredSevenDA_29207 : Nat.Prime 29207 := by norm_num

private theorem prime_oneHundredSevenDA_29879 : Nat.Prime 29879 := by norm_num

private theorem prime_oneHundredSevenDA_31019 : Nat.Prime 31019 := by norm_num

private theorem prime_oneHundredSevenDA_31741 : Nat.Prime 31741 := by norm_num

private theorem prime_oneHundredSevenDA_32771 : Nat.Prime 32771 := by norm_num

private theorem prime_oneHundredSevenDA_33013 : Nat.Prime 33013 := by norm_num

private theorem prime_oneHundredSevenDA_33587 : Nat.Prime 33587 := by norm_num

private theorem prime_oneHundredSevenDA_34061 : Nat.Prime 34061 := by norm_num

private theorem prime_oneHundredSevenDA_34747 : Nat.Prime 34747 := by norm_num

private theorem prime_oneHundredSevenDA_36901 : Nat.Prime 36901 := by norm_num

private theorem prime_oneHundredSevenDA_37573 : Nat.Prime 37573 := by norm_num

private theorem prime_oneHundredSevenDA_40841 : Nat.Prime 40841 := by norm_num

private theorem prime_oneHundredSevenDA_41579 : Nat.Prime 41579 := by norm_num

private theorem prime_oneHundredSevenDA_42571 : Nat.Prime 42571 := by norm_num

private theorem prime_oneHundredSevenDA_46567 : Nat.Prime 46567 := by norm_num

private theorem prime_oneHundredSevenDA_47903 : Nat.Prime 47903 := by norm_num

private theorem prime_oneHundredSevenDA_48481 : Nat.Prime 48481 := by norm_num

private theorem prime_oneHundredSevenDA_49103 : Nat.Prime 49103 := by norm_num

private theorem prime_oneHundredSevenDA_49369 : Nat.Prime 49369 := by norm_num

private theorem prime_oneHundredSevenDA_50951 : Nat.Prime 50951 := by norm_num

private theorem prime_oneHundredSevenDA_53161 : Nat.Prime 53161 := by norm_num

private theorem prime_oneHundredSevenDA_54377 : Nat.Prime 54377 := by norm_num

private theorem prime_oneHundredSevenDA_54709 : Nat.Prime 54709 := by norm_num

private theorem prime_oneHundredSevenDA_55229 : Nat.Prime 55229 := by norm_num

private theorem prime_oneHundredSevenDA_57727 : Nat.Prime 57727 := by norm_num

private theorem prime_oneHundredSevenDA_59029 : Nat.Prime 59029 := by norm_num

private theorem prime_oneHundredSevenDA_62213 : Nat.Prime 62213 := by norm_num

private theorem prime_oneHundredSevenDA_67307 : Nat.Prime 67307 := by norm_num

private theorem prime_oneHundredSevenDA_68161 : Nat.Prime 68161 := by norm_num

private theorem prime_oneHundredSevenDA_70621 : Nat.Prime 70621 := by norm_num

private theorem prime_oneHundredSevenDA_79139 : Nat.Prime 79139 := by norm_num

private theorem prime_oneHundredSevenDA_80923 : Nat.Prime 80923 := by norm_num

private theorem prime_oneHundredSevenDA_87931 : Nat.Prime 87931 := by norm_num

private theorem prime_oneHundredSevenDA_89227 : Nat.Prime 89227 := by norm_num

private theorem prime_oneHundredSevenDA_93703 : Nat.Prime 93703 := by norm_num

private theorem prime_oneHundredSevenDA_94117 : Nat.Prime 94117 := by norm_num

private theorem prime_oneHundredSevenDA_96293 : Nat.Prime 96293 := by norm_num

private theorem prime_oneHundredSevenDA_97919 : Nat.Prime 97919 := by norm_num

private theorem prime_oneHundredSevenDA_103951 : Nat.Prime 103951 := by norm_num

private theorem prime_oneHundredSevenDA_103997 : Nat.Prime 103997 := by norm_num

private theorem prime_oneHundredSevenDA_107119 : Nat.Prime 107119 := by norm_num

private theorem prime_oneHundredSevenDA_109547 : Nat.Prime 109547 := by norm_num

private theorem prime_oneHundredSevenDA_110933 : Nat.Prime 110933 := by norm_num

private theorem prime_oneHundredSevenDA_112799 : Nat.Prime 112799 := by norm_num

private theorem prime_oneHundredSevenDA_121357 : Nat.Prime 121357 := by norm_num

private theorem prime_oneHundredSevenDA_125219 : Nat.Prime 125219 := by norm_num

private theorem prime_oneHundredSevenDA_126097 : Nat.Prime 126097 := by norm_num

private theorem prime_oneHundredSevenDA_131927 : Nat.Prime 131927 := by norm_num

private theorem prime_oneHundredSevenDA_139663 : Nat.Prime 139663 := by norm_num

private theorem prime_oneHundredSevenDA_140759 : Nat.Prime 140759 := by norm_num

private theorem prime_oneHundredSevenDA_144073 : Nat.Prime 144073 := by norm_num

private theorem prime_oneHundredSevenDA_153281 : Nat.Prime 153281 := by norm_num

private theorem prime_oneHundredSevenDA_157273 : Nat.Prime 157273 := by norm_num

private theorem prime_oneHundredSevenDA_157559 : Nat.Prime 157559 := by norm_num

private theorem prime_oneHundredSevenDA_158419 : Nat.Prime 158419 := by norm_num

private theorem prime_oneHundredSevenDA_166597 : Nat.Prime 166597 := by norm_num

private theorem prime_oneHundredSevenDA_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredSevenDA_173897 : Nat.Prime 173897 := by norm_num

private theorem prime_oneHundredSevenDA_178921 : Nat.Prime 178921 := by norm_num

private theorem prime_oneHundredSevenDA_201947 : Nat.Prime 201947 := by norm_num

private theorem prime_oneHundredSevenDA_203761 : Nat.Prime 203761 := by norm_num

private theorem prime_oneHundredSevenDA_204359 : Nat.Prime 204359 := by norm_num

private theorem prime_oneHundredSevenDA_215239 : Nat.Prime 215239 := by norm_num

private theorem prime_oneHundredSevenDA_224569 : Nat.Prime 224569 := by norm_num

private theorem prime_oneHundredSevenDA_226283 : Nat.Prime 226283 := by norm_num

private theorem prime_oneHundredSevenDA_242413 : Nat.Prime 242413 := by norm_num

private theorem prime_oneHundredSevenDA_247829 : Nat.Prime 247829 := by norm_num

private theorem prime_oneHundredSevenDA_248683 : Nat.Prime 248683 := by norm_num

private theorem prime_oneHundredSevenDA_267097 : Nat.Prime 267097 := by norm_num

private theorem prime_oneHundredSevenDA_294923 : Nat.Prime 294923 := by norm_num

private theorem prime_oneHundredSevenDA_300299 : Nat.Prime 300299 := by norm_num

private theorem prime_oneHundredSevenDA_313127 : Nat.Prime 313127 := by norm_num

private theorem prime_oneHundredSevenDA_338531 : Nat.Prime 338531 := by norm_num

private theorem prime_oneHundredSevenDA_352549 : Nat.Prime 352549 := by norm_num

private theorem prime_oneHundredSevenDA_354953 : Nat.Prime 354953 := by norm_num

private theorem prime_oneHundredSevenDA_372497 : Nat.Prime 372497 := by norm_num

private theorem prime_oneHundredSevenDA_386249 : Nat.Prime 386249 := by norm_num

private theorem prime_oneHundredSevenDA_398267 : Nat.Prime 398267 := by norm_num

private theorem prime_oneHundredSevenDA_407249 : Nat.Prime 407249 := by norm_num

private theorem prime_oneHundredSevenDA_431831 : Nat.Prime 431831 := by norm_num

private theorem prime_oneHundredSevenDA_443563 : Nat.Prime 443563 := by norm_num

private theorem prime_oneHundredSevenDA_483971 : Nat.Prime 483971 := by norm_num

private theorem prime_oneHundredSevenDA_484853 : Nat.Prime 484853 := by norm_num

private theorem prime_oneHundredSevenDA_491353 : Nat.Prime 491353 := by norm_num

private theorem prime_oneHundredSevenDA_537877 : Nat.Prime 537877 := by norm_num

private theorem prime_oneHundredSevenDA_569659 : Nat.Prime 569659 := by norm_num

private theorem prime_oneHundredSevenDA_588463 : Nat.Prime 588463 := by norm_num

private theorem prime_oneHundredSevenDA_677077 : Nat.Prime 677077 := by norm_num

private theorem prime_oneHundredSevenDA_748343 : Nat.Prime 748343 := by norm_num

private theorem prime_oneHundredSevenDA_810659 : Nat.Prime 810659 := by norm_num

private theorem prime_oneHundredSevenDA_813443 : Nat.Prime 813443 := by norm_num

private theorem prime_oneHundredSevenDA_831967 : Nat.Prime 831967 := by norm_num

private theorem prime_oneHundredSevenDA_969467 : Nat.Prime 969467 := by norm_num

private theorem prime_oneHundredSevenDA_998161 : Nat.Prime 998161 := by norm_num

private theorem prime_oneHundredSevenDA_1028737 : Nat.Prime 1028737 := by norm_num

private theorem prime_oneHundredSevenDA_1043773 : Nat.Prime 1043773 := by norm_num

private theorem prime_oneHundredSevenDA_1087897 : Nat.Prime 1087897 := by norm_num

private theorem prime_oneHundredSevenDA_1104811 : Nat.Prime 1104811 := by norm_num

private theorem prime_oneHundredSevenDA_1238219 : Nat.Prime 1238219 := by norm_num

private theorem prime_oneHundredSevenDA_1240637 : Nat.Prime 1240637 := by norm_num

private theorem prime_oneHundredSevenDA_1306241 : Nat.Prime 1306241 := by norm_num

private theorem prime_oneHundredSevenDA_1315907 : Nat.Prime 1315907 := by norm_num

private theorem prime_oneHundredSevenDA_1410733 : Nat.Prime 1410733 := by norm_num

private theorem prime_oneHundredSevenDA_1410767 : Nat.Prime 1410767 := by norm_num

private theorem prime_oneHundredSevenDA_1472413 : Nat.Prime 1472413 := by norm_num

private theorem prime_oneHundredSevenDA_1518679 : Nat.Prime 1518679 := by norm_num

private theorem prime_oneHundredSevenDA_1748119 : Nat.Prime 1748119 := by norm_num

private theorem prime_oneHundredSevenDA_1781699 : Nat.Prime 1781699 := by norm_num

private theorem prime_oneHundredSevenDA_1787479 : Nat.Prime 1787479 := by norm_num

private theorem prime_oneHundredSevenDA_1923127 : Nat.Prime 1923127 := by norm_num

private theorem prime_oneHundredSevenDA_2047091 : Nat.Prime 2047091 := by norm_num

private theorem prime_oneHundredSevenDA_2070463 : Nat.Prime 2070463 := by norm_num

private theorem prime_oneHundredSevenDA_2138399 : Nat.Prime 2138399 := by norm_num

private theorem prime_oneHundredSevenDA_2141603 : Nat.Prime 2141603 := by norm_num

private theorem prime_oneHundredSevenDA_2258167 : Nat.Prime 2258167 := by norm_num

private theorem prime_oneHundredSevenDA_2430787 : Nat.Prime 2430787 := by norm_num

private theorem prime_oneHundredSevenDA_2456963 : Nat.Prime 2456963 := by norm_num

private theorem prime_oneHundredSevenDA_2615681 : Nat.Prime 2615681 := by norm_num

private theorem prime_oneHundredSevenDA_2638873 : Nat.Prime 2638873 := by norm_num

private theorem prime_oneHundredSevenDA_2876207 : Nat.Prime 2876207 := by norm_num

private theorem prime_oneHundredSevenDA_2911079 : Nat.Prime 2911079 := by norm_num

private theorem prime_oneHundredSevenDA_3638753 : Nat.Prime 3638753 := by norm_num

private theorem prime_oneHundredSevenDA_3640909 : Nat.Prime 3640909 := by norm_num

private theorem prime_oneHundredSevenDA_3744701 : Nat.Prime 3744701 := by norm_num

private theorem prime_oneHundredSevenDA_3779359 : Nat.Prime 3779359 := by norm_num

private theorem prime_oneHundredSevenDA_3988249 : Nat.Prime 3988249 := by norm_num

private theorem prime_oneHundredSevenDA_4138747 : Nat.Prime 4138747 := by norm_num

private theorem prime_oneHundredSevenDA_4336589 : Nat.Prime 4336589 := by norm_num

private theorem prime_oneHundredSevenDA_4367557 : Nat.Prime 4367557 := by norm_num

private theorem prime_oneHundredSevenDA_4809307 : Nat.Prime 4809307 := by norm_num

private theorem prime_oneHundredSevenDA_5096393 : Nat.Prime 5096393 := by norm_num

private theorem prime_oneHundredSevenDA_5098567 : Nat.Prime 5098567 := by norm_num

private theorem prime_oneHundredSevenDA_5276501 : Nat.Prime 5276501 := by norm_num

private theorem prime_oneHundredSevenDA_5276833 : Nat.Prime 5276833 := by norm_num

private theorem prime_oneHundredSevenDA_5624849 : Nat.Prime 5624849 := by norm_num

private theorem prime_oneHundredSevenDA_5997791 : Nat.Prime 5997791 := by norm_num

private theorem prime_oneHundredSevenDA_6026197 : Nat.Prime 6026197 := by norm_num

private theorem prime_oneHundredSevenDA_6087233 : Nat.Prime 6087233 := by norm_num

private theorem prime_oneHundredSevenDA_6905533 : Nat.Prime 6905533 := by norm_num

private theorem prime_oneHundredSevenDA_6924263 : Nat.Prime 6924263 := by norm_num

private theorem prime_oneHundredSevenDA_6960719 : Nat.Prime 6960719 := by norm_num

private theorem prime_oneHundredSevenDA_7141349 : Nat.Prime 7141349 := by norm_num

private theorem prime_oneHundredSevenDA_7172189 : Nat.Prime 7172189 := by norm_num

private theorem prime_oneHundredSevenDA_7264813 : Nat.Prime 7264813 := by norm_num

private theorem prime_oneHundredSevenDA_8048303 : Nat.Prime 8048303 := by norm_num

private theorem prime_oneHundredSevenDA_8503631 : Nat.Prime 8503631 := by norm_num

private theorem prime_oneHundredSevenDA_9036589 : Nat.Prime 9036589 := by norm_num

private theorem prime_oneHundredSevenDA_9061667 : Nat.Prime 9061667 := by norm_num

private theorem prime_oneHundredSevenDA_9824323 : Nat.Prime 9824323 := by norm_num

private theorem prime_oneHundredSevenDA_10197893 : Nat.Prime 10197893 := by norm_num

private theorem prime_oneHundredSevenDA_10325599 : Nat.Prime 10325599 := by norm_num

private theorem prime_oneHundredSevenDA_10427237 : Nat.Prime 10427237 := by norm_num

private theorem prime_oneHundredSevenDA_10478621 : Nat.Prime 10478621 := by norm_num

private theorem prime_oneHundredSevenDA_10549397 : Nat.Prime 10549397 := by norm_num

private theorem prime_oneHundredSevenDA_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredSevenDA_10968259 : Nat.Prime 10968259 := by norm_num

private theorem prime_oneHundredSevenDA_12406997 : Nat.Prime 12406997 := by norm_num

private theorem prime_oneHundredSevenDA_12826733 : Nat.Prime 12826733 := by norm_num

private theorem prime_oneHundredSevenDA_12846887 : Nat.Prime 12846887 := by norm_num

private theorem prime_oneHundredSevenDA_13408621 : Nat.Prime 13408621 := by norm_num

private theorem prime_oneHundredSevenDA_14140981 : Nat.Prime 14140981 := by norm_num

private theorem prime_oneHundredSevenDA_14223953 : Nat.Prime 14223953 := by norm_num

private theorem prime_oneHundredSevenDA_14759873 : Nat.Prime 14759873 := by norm_num

private theorem prime_oneHundredSevenDA_14818663 : Nat.Prime 14818663 := by norm_num

private theorem prime_oneHundredSevenDA_14844367 : Nat.Prime 14844367 := by norm_num

private theorem prime_oneHundredSevenDA_15839861 : Nat.Prime 15839861 := by norm_num

private theorem prime_oneHundredSevenDA_15919741 : Nat.Prime 15919741 := by norm_num

private theorem prime_oneHundredSevenDA_16332011 : Nat.Prime 16332011 := by norm_num

private theorem prime_oneHundredSevenDA_17521703 : Nat.Prime 17521703 := by norm_num

private theorem prime_oneHundredSevenDA_17560409 : Nat.Prime 17560409 := by norm_num

private theorem prime_oneHundredSevenDA_17678981 : Nat.Prime 17678981 := by norm_num

private theorem prime_oneHundredSevenDA_17700997 : Nat.Prime 17700997 := by norm_num

private theorem prime_oneHundredSevenDA_17778029 : Nat.Prime 17778029 := by norm_num

private theorem prime_oneHundredSevenDA_21476747 : Nat.Prime 21476747 := by norm_num

private theorem prime_oneHundredSevenDA_21877369 : Nat.Prime 21877369 := by norm_num

private theorem prime_oneHundredSevenDA_22937479 : Nat.Prime 22937479 := by norm_num

private theorem prime_oneHundredSevenDA_23686541 : Nat.Prime 23686541 := by norm_num

private theorem prime_oneHundredSevenDA_23817271 : Nat.Prime 23817271 := by norm_num

private theorem prime_oneHundredSevenDA_26161969 : Nat.Prime 26161969 := by norm_num

private theorem prime_oneHundredSevenDA_27166303 : Nat.Prime 27166303 := by norm_num

private theorem prime_oneHundredSevenDA_27502483 : Nat.Prime 27502483 := by norm_num

private theorem prime_oneHundredSevenDA_27795379 : Nat.Prime 27795379 := by norm_num

private theorem prime_oneHundredSevenDA_30109309 : Nat.Prime 30109309 := by
  apply lucas_primality 30109309 (10 : ZMod 30109309)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (29, 1), (31, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (29, 1), (31, 1), (2791, 1)] : List FactorBlock).map factorBlockValue).prod) = 30109309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_2791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 30109309) ^ 15054654 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30109309) ^ 10036436 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30109309) ^ 1038252 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30109309) ^ 971268 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30109309) ^ 10788 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_30703877 : Nat.Prime 30703877 := by
  apply lucas_primality 30703877 (2 : ZMod 30703877)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (211, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (211, 1), (5197, 1)] : List FactorBlock).map factorBlockValue).prod) = 30703877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_211
      · exact prime_oneHundredSevenDA_5197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 30703877) ^ 15351938 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30703877) ^ 4386268 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30703877) ^ 145516 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 30703877) ^ 5908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_31342963 : Nat.Prime 31342963 := by
  apply lucas_primality 31342963 (2 : ZMod 31342963)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (401, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (401, 1), (1861, 1)] : List FactorBlock).map factorBlockValue).prod) = 31342963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_401
      · exact prime_oneHundredSevenDA_1861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31342963) ^ 15671481 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31342963) ^ 10447654 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31342963) ^ 4477566 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31342963) ^ 78162 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31342963) ^ 16842 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_31679723 : Nat.Prime 31679723 := by
  apply lucas_primality 31679723 (2 : ZMod 31679723)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (15839861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (15839861, 1)] : List FactorBlock).map factorBlockValue).prod) = 31679723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_15839861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 31679723) ^ 15839861 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 31679723) ^ 2 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_32396321 : Nat.Prime 32396321 := by
  apply lucas_primality 32396321 (3 : ZMod 32396321)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (11, 1), (79, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (11, 1), (79, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 32396321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_79
      · exact prime_oneHundredSevenDA_233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 32396321) ^ 16198160 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 32396321) ^ 6479264 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 32396321) ^ 2945120 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 32396321) ^ 410080 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 32396321) ^ 139040 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_34164607 : Nat.Prime 34164607 := by
  apply lucas_primality 34164607 (6 : ZMod 34164607)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (813443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (813443, 1)] : List FactorBlock).map factorBlockValue).prod) = 34164607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_813443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 34164607) ^ 17082303 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 34164607) ^ 11388202 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 34164607) ^ 4880658 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 34164607) ^ 42 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_35357963 : Nat.Prime 35357963 := by
  apply lucas_primality 35357963 (2 : ZMod 35357963)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17678981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17678981, 1)] : List FactorBlock).map factorBlockValue).prod) = 35357963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_17678981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 35357963) ^ 17678981 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35357963) ^ 2 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_35813251 : Nat.Prime 35813251 := by
  apply lucas_primality 35813251 (2 : ZMod 35813251)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 3), (11, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 3), (11, 1), (1447, 1)] : List FactorBlock).map factorBlockValue).prod) = 35813251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_1447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35813251) ^ 17906625 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35813251) ^ 11937750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35813251) ^ 7162650 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35813251) ^ 3255750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 35813251) ^ 24750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_36097877 : Nat.Prime 36097877 := by
  apply lucas_primality 36097877 (2 : ZMod 36097877)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (53, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (53, 1), (4153, 1)] : List FactorBlock).map factorBlockValue).prod) = 36097877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_53
      · exact prime_oneHundredSevenDA_4153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 36097877) ^ 18048938 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36097877) ^ 880436 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36097877) ^ 681092 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 36097877) ^ 8692 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_39187231 : Nat.Prime 39187231 := by
  apply lucas_primality 39187231 (6 : ZMod 39187231)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1306241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1306241, 1)] : List FactorBlock).map factorBlockValue).prod) = 39187231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_1306241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 39187231) ^ 19593615 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39187231) ^ 13062410 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39187231) ^ 7837446 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 39187231) ^ 30 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_47268547 : Nat.Prime 47268547 := by
  apply lucas_primality 47268547 (3 : ZMod 47268547)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (691, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (691, 1), (877, 1)] : List FactorBlock).map factorBlockValue).prod) = 47268547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_691
      · exact prime_oneHundredSevenDA_877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 47268547) ^ 23634273 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47268547) ^ 15756182 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47268547) ^ 3636042 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47268547) ^ 68406 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47268547) ^ 53898 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_49158409 : Nat.Prime 49158409 := by
  apply lucas_primality 49158409 (7 : ZMod 49158409)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (157559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (157559, 1)] : List FactorBlock).map factorBlockValue).prod) = 49158409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_157559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 49158409) ^ 24579204 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 49158409) ^ 16386136 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 49158409) ^ 3781416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 49158409) ^ 312 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_49633973 : Nat.Prime 49633973 := by
  apply lucas_primality 49633973 (2 : ZMod 49633973)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (797, 1), (15569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (797, 1), (15569, 1)] : List FactorBlock).map factorBlockValue).prod) = 49633973 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_797
      · exact prime_oneHundredSevenDA_15569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 49633973) ^ 24816986 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 49633973) ^ 62276 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 49633973) ^ 3188 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_54896839 : Nat.Prime 54896839 := by
  apply lucas_primality 54896839 (3 : ZMod 54896839)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (191, 1), (47903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (191, 1), (47903, 1)] : List FactorBlock).map factorBlockValue).prod) = 54896839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_191
      · exact prime_oneHundredSevenDA_47903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 54896839) ^ 27448419 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54896839) ^ 18298946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54896839) ^ 287418 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 54896839) ^ 1146 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_56617307 : Nat.Prime 56617307 := by
  apply lucas_primality 56617307 (5 : ZMod 56617307)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (727, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (727, 1), (1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 56617307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_727
      · exact prime_oneHundredSevenDA_1693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 56617307) ^ 28308653 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56617307) ^ 2461622 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56617307) ^ 77878 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 56617307) ^ 33442 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_58086601 : Nat.Prime 58086601 := by
  apply lucas_primality 58086601 (14 : ZMod 58086601)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (11, 1), (13, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (11, 1), (13, 1), (677, 1)] : List FactorBlock).map factorBlockValue).prod) = 58086601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 58086601) ^ 29043300 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 58086601) ^ 19362200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 58086601) ^ 11617320 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 58086601) ^ 5280600 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 58086601) ^ 4468200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 58086601) ^ 85800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_60712247 : Nat.Prime 60712247 := by
  apply lucas_primality 60712247 (5 : ZMod 60712247)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4336589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4336589, 1)] : List FactorBlock).map factorBlockValue).prod) = 60712247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_4336589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 60712247) ^ 30356123 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60712247) ^ 8673178 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60712247) ^ 14 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_74129603 : Nat.Prime 74129603 := by
  apply lucas_primality 74129603 (2 : ZMod 74129603)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (73, 1), (26723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (73, 1), (26723, 1)] : List FactorBlock).map factorBlockValue).prod) = 74129603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_73
      · exact prime_oneHundredSevenDA_26723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 74129603) ^ 37064801 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74129603) ^ 3901558 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74129603) ^ 1015474 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74129603) ^ 2774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_79848623 : Nat.Prime 79848623 := by
  apply lucas_primality 79848623 (5 : ZMod 79848623)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (251, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (251, 1), (733, 1)] : List FactorBlock).map factorBlockValue).prod) = 79848623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_251
      · exact prime_oneHundredSevenDA_733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 79848623) ^ 39924311 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 79848623) ^ 11406946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 79848623) ^ 2575762 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 79848623) ^ 318122 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 79848623) ^ 108934 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_80946863 : Nat.Prime 80946863 := by
  apply lucas_primality 80946863 (5 : ZMod 80946863)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (991, 1), (40841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (991, 1), (40841, 1)] : List FactorBlock).map factorBlockValue).prod) = 80946863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_991
      · exact prime_oneHundredSevenDA_40841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 80946863) ^ 40473431 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 80946863) ^ 81682 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 80946863) ^ 1982 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_81656879 : Nat.Prime 81656879 := by
  apply lucas_primality 81656879 (13 : ZMod 81656879)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (599, 1), (68161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (599, 1), (68161, 1)] : List FactorBlock).map factorBlockValue).prod) = 81656879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_599
      · exact prime_oneHundredSevenDA_68161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 81656879) ^ 40828439 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 81656879) ^ 136322 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 81656879) ^ 1198 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_96939683 : Nat.Prime 96939683 := by
  apply lucas_primality 96939683 (2 : ZMod 96939683)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (6924263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (6924263, 1)] : List FactorBlock).map factorBlockValue).prod) = 96939683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_6924263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 96939683) ^ 48469841 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 96939683) ^ 13848526 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 96939683) ^ 14 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_103192447 : Nat.Prime 103192447 := by
  apply lucas_primality 103192447 (3 : ZMod 103192447)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (2456963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (2456963, 1)] : List FactorBlock).map factorBlockValue).prod) = 103192447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_2456963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 103192447) ^ 51596223 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103192447) ^ 34397482 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103192447) ^ 14741778 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 103192447) ^ 42 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_103956529 : Nat.Prime 103956529 := by
  apply lucas_primality 103956529 (7 : ZMod 103956529)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (166597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (166597, 1)] : List FactorBlock).map factorBlockValue).prod) = 103956529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_166597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 103956529) ^ 51978264 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 103956529) ^ 34652176 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 103956529) ^ 7996656 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 103956529) ^ 624 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_105808783 : Nat.Prime 105808783 := by
  apply lucas_primality 105808783 (5 : ZMod 105808783)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (41, 1), (25301, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (41, 1), (25301, 1)] : List FactorBlock).map factorBlockValue).prod) = 105808783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_25301
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 105808783) ^ 52904391 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105808783) ^ 35269594 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105808783) ^ 6224046 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105808783) ^ 2580702 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 105808783) ^ 4182 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_109957231 : Nat.Prime 109957231 := by
  apply lucas_primality 109957231 (6 : ZMod 109957231)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (407249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (407249, 1)] : List FactorBlock).map factorBlockValue).prod) = 109957231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_407249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 109957231) ^ 54978615 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 109957231) ^ 36652410 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 109957231) ^ 21991446 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 109957231) ^ 270 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_110203157 : Nat.Prime 110203157 := by
  apply lucas_primality 110203157 (2 : ZMod 110203157)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 3), (47, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 3), (47, 1), (1709, 1)] : List FactorBlock).map factorBlockValue).prod) = 110203157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_47
      · exact prime_oneHundredSevenDA_1709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 110203157) ^ 55101578 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 110203157) ^ 15743308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 110203157) ^ 2344748 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 110203157) ^ 64484 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_130656089 : Nat.Prime 130656089 := by
  apply lucas_primality 130656089 (3 : ZMod 130656089)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (16332011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (16332011, 1)] : List FactorBlock).map factorBlockValue).prod) = 130656089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_16332011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 130656089) ^ 65328044 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 130656089) ^ 8 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_133405541 : Nat.Prime 133405541 := by
  apply lucas_primality 133405541 (2 : ZMod 133405541)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (113, 1), (59029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (113, 1), (59029, 1)] : List FactorBlock).map factorBlockValue).prod) = 133405541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_113
      · exact prime_oneHundredSevenDA_59029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 133405541) ^ 66702770 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 133405541) ^ 26681108 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 133405541) ^ 1180580 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 133405541) ^ 2260 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_135596567 : Nat.Prime 135596567 := by
  apply lucas_primality 135596567 (5 : ZMod 135596567)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (593, 1), (16333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (593, 1), (16333, 1)] : List FactorBlock).map factorBlockValue).prod) = 135596567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_593
      · exact prime_oneHundredSevenDA_16333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 135596567) ^ 67798283 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135596567) ^ 19370938 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135596567) ^ 228662 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 135596567) ^ 8302 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_138105601 : Nat.Prime 138105601 := by
  apply lucas_primality 138105601 (11 : ZMod 138105601)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (7193, 1)] : List FactorBlock).map factorBlockValue).prod) = 138105601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 138105601) ^ 69052800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 138105601) ^ 46035200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 138105601) ^ 27621120 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 138105601) ^ 19200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_141857549 : Nat.Prime 141857549 := by
  apply lucas_primality 141857549 (2 : ZMod 141857549)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (199, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (199, 1), (3637, 1)] : List FactorBlock).map factorBlockValue).prod) = 141857549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_199
      · exact prime_oneHundredSevenDA_3637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 141857549) ^ 70928774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141857549) ^ 20265364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141857549) ^ 712852 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 141857549) ^ 39004 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_150728951 : Nat.Prime 150728951 := by
  apply lucas_primality 150728951 (7 : ZMod 150728951)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (29, 1), (103951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (29, 1), (103951, 1)] : List FactorBlock).map factorBlockValue).prod) = 150728951 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_103951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 150728951) ^ 75364475 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 150728951) ^ 30145790 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 150728951) ^ 5197550 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 150728951) ^ 1450 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_180637661 : Nat.Prime 180637661 := by
  apply lucas_primality 180637661 (3 : ZMod 180637661)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (1087, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (1087, 1), (1187, 1)] : List FactorBlock).map factorBlockValue).prod) = 180637661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_1087
      · exact prime_oneHundredSevenDA_1187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 180637661) ^ 90318830 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 180637661) ^ 36127532 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 180637661) ^ 25805380 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 180637661) ^ 166180 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 180637661) ^ 152180 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_195715283 : Nat.Prime 195715283 := by
  apply lucas_primality 195715283 (2 : ZMod 195715283)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (739, 1), (18917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (739, 1), (18917, 1)] : List FactorBlock).map factorBlockValue).prod) = 195715283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_739
      · exact prime_oneHundredSevenDA_18917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 195715283) ^ 97857641 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 195715283) ^ 27959326 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 195715283) ^ 264838 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 195715283) ^ 10346 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_196609087 : Nat.Prime 196609087 := by
  apply lucas_primality 196609087 (3 : ZMod 196609087)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (3640909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (3640909, 1)] : List FactorBlock).map factorBlockValue).prod) = 196609087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_3640909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 196609087) ^ 98304543 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 196609087) ^ 65536362 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 196609087) ^ 54 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_203942681 : Nat.Prime 203942681 := by
  apply lucas_primality 203942681 (3 : ZMod 203942681)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (5098567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (5098567, 1)] : List FactorBlock).map factorBlockValue).prod) = 203942681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_5098567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 203942681) ^ 101971340 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 203942681) ^ 40788536 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 203942681) ^ 40 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_256199863 : Nat.Prime 256199863 := by
  apply lucas_primality 256199863 (3 : ZMod 256199863)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (1472413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (1472413, 1)] : List FactorBlock).map factorBlockValue).prod) = 256199863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_1472413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 256199863) ^ 128099931 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 256199863) ^ 85399954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 256199863) ^ 8834478 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 256199863) ^ 174 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_264446459 : Nat.Prime 264446459 := by
  apply lucas_primality 264446459 (7 : ZMod 264446459)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (71, 1), (109547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (71, 1), (109547, 1)] : List FactorBlock).map factorBlockValue).prod) = 264446459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_71
      · exact prime_oneHundredSevenDA_109547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 264446459) ^ 132223229 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 264446459) ^ 15555674 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 264446459) ^ 3724598 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 264446459) ^ 2414 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_274424333 : Nat.Prime 274424333 := by
  apply lucas_primality 274424333 (3 : ZMod 274424333)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (25997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (25997, 1)] : List FactorBlock).map factorBlockValue).prod) = 274424333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_25997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 274424333) ^ 137212166 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 274424333) ^ 39203476 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 274424333) ^ 21109564 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 274424333) ^ 9462908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 274424333) ^ 10556 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_277833683 : Nat.Prime 277833683 := by
  apply lucas_primality 277833683 (2 : ZMod 277833683)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2017, 1), (9839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2017, 1), (9839, 1)] : List FactorBlock).map factorBlockValue).prod) = 277833683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_2017
      · exact prime_oneHundredSevenDA_9839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 277833683) ^ 138916841 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 277833683) ^ 39690526 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 277833683) ^ 137746 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 277833683) ^ 28238 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_329997817 : Nat.Prime 329997817 := by
  apply lucas_primality 329997817 (5 : ZMod 329997817)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (127, 1), (151, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (127, 1), (151, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 329997817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_127
      · exact prime_oneHundredSevenDA_151
      · exact prime_oneHundredSevenDA_239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 329997817) ^ 164998908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 329997817) ^ 109999272 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 329997817) ^ 2598408 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 329997817) ^ 2185416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 329997817) ^ 1380744 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_376115557 : Nat.Prime 376115557 := by
  apply lucas_primality 376115557 (2 : ZMod 376115557)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31342963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31342963, 1)] : List FactorBlock).map factorBlockValue).prod) = 376115557 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_31342963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 376115557) ^ 188057778 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 376115557) ^ 125371852 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 376115557) ^ 12 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_407711441 : Nat.Prime 407711441 := by
  apply lucas_primality 407711441 (3 : ZMod 407711441)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (5096393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (5096393, 1)] : List FactorBlock).map factorBlockValue).prod) = 407711441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_5096393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 407711441) ^ 203855720 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 407711441) ^ 81542288 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 407711441) ^ 80 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_433756273 : Nat.Prime 433756273 := by
  apply lucas_primality 433756273 (5 : ZMod 433756273)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (9036589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (9036589, 1)] : List FactorBlock).map factorBlockValue).prod) = 433756273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_9036589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 433756273) ^ 216878136 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 433756273) ^ 144585424 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 433756273) ^ 48 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_441333181 : Nat.Prime 441333181 := by
  apply lucas_primality 441333181 (6 : ZMod 441333181)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (73, 1), (33587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (73, 1), (33587, 1)] : List FactorBlock).map factorBlockValue).prod) = 441333181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_73
      · exact prime_oneHundredSevenDA_33587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 441333181) ^ 220666590 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 441333181) ^ 147111060 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 441333181) ^ 88266636 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 441333181) ^ 6045660 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 441333181) ^ 13140 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_469929349 : Nat.Prime 469929349 := by
  apply lucas_primality 469929349 (6 : ZMod 469929349)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (1181, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (1181, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 469929349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_1181
      · exact prime_oneHundredSevenDA_1579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 469929349) ^ 234964674 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 469929349) ^ 156643116 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 469929349) ^ 67132764 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 469929349) ^ 397908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 469929349) ^ 297612 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_479997197 : Nat.Prime 479997197 := by
  apply lucas_primality 479997197 (2 : ZMod 479997197)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (109, 1), (157273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (109, 1), (157273, 1)] : List FactorBlock).map factorBlockValue).prod) = 479997197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_109
      · exact prime_oneHundredSevenDA_157273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 479997197) ^ 239998598 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 479997197) ^ 68571028 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 479997197) ^ 4403644 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 479997197) ^ 3052 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_506371057 : Nat.Prime 506371057 := by
  apply lucas_primality 506371057 (7 : ZMod 506371057)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (10549397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (10549397, 1)] : List FactorBlock).map factorBlockValue).prod) = 506371057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_10549397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 506371057) ^ 253185528 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 506371057) ^ 168790352 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 506371057) ^ 48 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_530512487 : Nat.Prime 530512487 := by
  apply lucas_primality 530512487 (5 : ZMod 530512487)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (29, 1), (31, 1), (61, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (29, 1), (31, 1), (61, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 530512487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_61
      · exact prime_oneHundredSevenDA_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 530512487) ^ 265256243 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 530512487) ^ 75787498 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 530512487) ^ 18293534 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 530512487) ^ 17113306 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 530512487) ^ 8696926 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 530512487) ^ 767746 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_548848667 : Nat.Prime 548848667 := by
  apply lucas_primality 548848667 (2 : ZMod 548848667)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (274424333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (274424333, 1)] : List FactorBlock).map factorBlockValue).prod) = 548848667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_274424333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 548848667) ^ 274424333 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 548848667) ^ 2 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_555667367 : Nat.Prime 555667367 := by
  apply lucas_primality 555667367 (5 : ZMod 555667367)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (277833683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (277833683, 1)] : List FactorBlock).map factorBlockValue).prod) = 555667367 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_277833683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 555667367) ^ 277833683 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 555667367) ^ 2 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_580984003 : Nat.Prime 580984003 := by
  apply lucas_primality 580984003 (2 : ZMod 580984003)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (23, 1), (241, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (23, 1), (241, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 580984003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_241
      · exact prime_oneHundredSevenDA_647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 580984003) ^ 290492001 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 580984003) ^ 193661334 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 580984003) ^ 25260174 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 580984003) ^ 2410722 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 580984003) ^ 897966 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_17203
      · exact prime_oneHundredSevenDA_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_733930481 : Nat.Prime 733930481 := by
  apply lucas_primality 733930481 (6 : ZMod 733930481)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (19, 1), (113, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (19, 1), (113, 1), (4273, 1)] : List FactorBlock).map factorBlockValue).prod) = 733930481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_113
      · exact prime_oneHundredSevenDA_4273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 733930481) ^ 366965240 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 733930481) ^ 146786096 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 733930481) ^ 38627920 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 733930481) ^ 6494960 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 733930481) ^ 171760 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_756296753 : Nat.Prime 756296753 := by
  apply lucas_primality 756296753 (3 : ZMod 756296753)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (47268547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (47268547, 1)] : List FactorBlock).map factorBlockValue).prod) = 756296753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_47268547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 756296753) ^ 378148376 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 756296753) ^ 16 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_813324487 : Nat.Prime 813324487 := by
  apply lucas_primality 813324487 (5 : ZMod 813324487)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (10427237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (10427237, 1)] : List FactorBlock).map factorBlockValue).prod) = 813324487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_10427237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 813324487) ^ 406662243 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 813324487) ^ 271108162 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 813324487) ^ 62563422 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 813324487) ^ 78 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_838079087 : Nat.Prime 838079087 := by
  apply lucas_primality 838079087 (10 : ZMod 838079087)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (229, 1), (140759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (229, 1), (140759, 1)] : List FactorBlock).map factorBlockValue).prod) = 838079087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_229
      · exact prime_oneHundredSevenDA_140759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 838079087) ^ 419039543 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 838079087) ^ 64467622 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 838079087) ^ 3659734 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 838079087) ^ 5954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_905271541 : Nat.Prime 905271541 := by
  apply lucas_primality 905271541 (2 : ZMod 905271541)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (29, 1), (73, 1), (7127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (29, 1), (73, 1), (7127, 1)] : List FactorBlock).map factorBlockValue).prod) = 905271541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_73
      · exact prime_oneHundredSevenDA_7127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 905271541) ^ 452635770 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 905271541) ^ 301757180 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 905271541) ^ 181054308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 905271541) ^ 31216260 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 905271541) ^ 12400980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 905271541) ^ 127020 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_958183477 : Nat.Prime 958183477 := by
  apply lucas_primality 958183477 (7 : ZMod 958183477)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (79848623, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (79848623, 1)] : List FactorBlock).map factorBlockValue).prod) = 958183477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_79848623
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 958183477) ^ 479091738 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 958183477) ^ 319394492 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 958183477) ^ 12 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1058087831 : Nat.Prime 1058087831 := by
  apply lucas_primality 1058087831 (11 : ZMod 1058087831)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (105808783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (105808783, 1)] : List FactorBlock).map factorBlockValue).prod) = 1058087831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_105808783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1058087831) ^ 529043915 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1058087831) ^ 211617566 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1058087831) ^ 10 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1133569847 : Nat.Prime 1133569847 := by
  apply lucas_primality 1133569847 (5 : ZMod 1133569847)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (2287, 1), (247829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (2287, 1), (247829, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133569847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_2287
      · exact prime_oneHundredSevenDA_247829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1133569847) ^ 566784923 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1133569847) ^ 495658 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1133569847) ^ 4574 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1136242999 : Nat.Prime 1136242999 := by
  apply lucas_primality 1136242999 (3 : ZMod 1136242999)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (11, 2), (173897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (11, 2), (173897, 1)] : List FactorBlock).map factorBlockValue).prod) = 1136242999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_173897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1136242999) ^ 568121499 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1136242999) ^ 378747666 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1136242999) ^ 103294818 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1136242999) ^ 6534 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1179958649 : Nat.Prime 1179958649 := by
  apply lucas_primality 1179958649 (3 : ZMod 1179958649)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (13408621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (13408621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1179958649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_13408621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1179958649) ^ 589979324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1179958649) ^ 107268968 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1179958649) ^ 88 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1218431017 : Nat.Prime 1218431017 := by
  apply lucas_primality 1218431017 (5 : ZMod 1218431017)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (37, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (37, 1), (41579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1218431017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_41579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1218431017) ^ 609215508 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1218431017) ^ 406143672 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1218431017) ^ 110766456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1218431017) ^ 32930568 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1218431017) ^ 29304 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1393907813 : Nat.Prime 1393907813 := by
  apply lucas_primality 1393907813 (2 : ZMod 1393907813)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (31679723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (31679723, 1)] : List FactorBlock).map factorBlockValue).prod) = 1393907813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_31679723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1393907813) ^ 696953906 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393907813) ^ 126718892 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1393907813) ^ 44 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1404891569 : Nat.Prime 1404891569 := by
  apply lucas_primality 1404891569 (3 : ZMod 1404891569)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (2141603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (2141603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1404891569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_2141603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1404891569) ^ 702445784 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1404891569) ^ 34265648 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1404891569) ^ 656 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1565008591 : Nat.Prime 1565008591 := by
  apply lucas_primality 1565008591 (3 : ZMod 1565008591)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (487, 1), (107119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (487, 1), (107119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1565008591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_487
      · exact prime_oneHundredSevenDA_107119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1565008591) ^ 782504295 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565008591) ^ 521669530 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565008591) ^ 313001718 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565008591) ^ 3213570 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1565008591) ^ 14610 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1571571923 : Nat.Prime 1571571923 := by
  apply lucas_primality 1571571923 (2 : ZMod 1571571923)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (34164607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (34164607, 1)] : List FactorBlock).map factorBlockValue).prod) = 1571571923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_34164607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1571571923) ^ 785785961 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1571571923) ^ 68329214 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1571571923) ^ 46 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1710719201 : Nat.Prime 1710719201 := by
  apply lucas_primality 1710719201 (3 : ZMod 1710719201)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (2138399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (2138399, 1)] : List FactorBlock).map factorBlockValue).prod) = 1710719201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_2138399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1710719201) ^ 855359600 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1710719201) ^ 342143840 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1710719201) ^ 800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1842034067 : Nat.Prime 1842034067 := by
  apply lucas_primality 1842034067 (2 : ZMod 1842034067)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3067, 1), (300299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3067, 1), (300299, 1)] : List FactorBlock).map factorBlockValue).prod) = 1842034067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3067
      · exact prime_oneHundredSevenDA_300299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1842034067) ^ 921017033 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1842034067) ^ 600598 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1842034067) ^ 6134 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_2446568239 : Nat.Prime 2446568239 := by
  apply lucas_primality 2446568239 (3 : ZMod 2446568239)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 2), (484853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 2), (484853, 1)] : List FactorBlock).map factorBlockValue).prod) = 2446568239 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_484853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2446568239) ^ 1223284119 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446568239) ^ 815522746 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446568239) ^ 84364422 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 2446568239) ^ 5046 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_2562718481 : Nat.Prime 2562718481 := by
  apply lucas_primality 2562718481 (13 : ZMod 2562718481)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (19, 1), (107, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (19, 1), (107, 1), (2251, 1)] : List FactorBlock).map factorBlockValue).prod) = 2562718481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_107
      · exact prime_oneHundredSevenDA_2251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 2562718481) ^ 1281359240 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2562718481) ^ 512543696 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2562718481) ^ 366102640 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2562718481) ^ 134879920 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2562718481) ^ 23950640 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 2562718481) ^ 1138480 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3035612351 : Nat.Prime 3035612351 := by
  apply lucas_primality 3035612351 (13 : ZMod 3035612351)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (60712247, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (60712247, 1)] : List FactorBlock).map factorBlockValue).prod) = 3035612351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_60712247
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3035612351) ^ 1517806175 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 3035612351) ^ 607122470 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 3035612351) ^ 50 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3052121263 : Nat.Prime 3052121263 := by
  apply lucas_primality 3052121263 (5 : ZMod 3052121263)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (41, 1), (12406997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (41, 1), (12406997, 1)] : List FactorBlock).map factorBlockValue).prod) = 3052121263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_12406997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3052121263) ^ 1526060631 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3052121263) ^ 1017373754 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3052121263) ^ 74441982 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3052121263) ^ 246 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3106545787 : Nat.Prime 3106545787 := by
  apply lucas_primality 3106545787 (2 : ZMod 3106545787)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (71, 1), (2430787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (71, 1), (2430787, 1)] : List FactorBlock).map factorBlockValue).prod) = 3106545787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_71
      · exact prime_oneHundredSevenDA_2430787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3106545787) ^ 1553272893 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3106545787) ^ 1035515262 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3106545787) ^ 43754166 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3106545787) ^ 1278 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3264436163 : Nat.Prime 3264436163 := by
  apply lucas_primality 3264436163 (2 : ZMod 3264436163)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (89, 1), (1410733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (89, 1), (1410733, 1)] : List FactorBlock).map factorBlockValue).prod) = 3264436163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_89
      · exact prime_oneHundredSevenDA_1410733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3264436163) ^ 1632218081 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3264436163) ^ 251110474 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3264436163) ^ 36679058 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3264436163) ^ 2314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3416729753 : Nat.Prime 3416729753 := by
  apply lucas_primality 3416729753 (3 : ZMod 3416729753)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 1), (211, 1), (49369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 1), (211, 1), (49369, 1)] : List FactorBlock).map factorBlockValue).prod) = 3416729753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_211
      · exact prime_oneHundredSevenDA_49369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3416729753) ^ 1708364876 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3416729753) ^ 83334872 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3416729753) ^ 16193032 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3416729753) ^ 69208 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3540213863 : Nat.Prime 3540213863 := by
  apply lucas_primality 3540213863 (5 : ZMod 3540213863)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5653, 1), (313127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5653, 1), (313127, 1)] : List FactorBlock).map factorBlockValue).prod) = 3540213863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5653
      · exact prime_oneHundredSevenDA_313127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3540213863) ^ 1770106931 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3540213863) ^ 626254 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 3540213863) ^ 11306 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3623171269 : Nat.Prime 3623171269 := by
  apply lucas_primality 3623171269 (2 : ZMod 3623171269)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (157, 1), (1923127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (157, 1), (1923127, 1)] : List FactorBlock).map factorBlockValue).prod) = 3623171269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_157
      · exact prime_oneHundredSevenDA_1923127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3623171269) ^ 1811585634 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3623171269) ^ 1207723756 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3623171269) ^ 23077524 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3623171269) ^ 1884 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4083688121 : Nat.Prime 4083688121 := by
  apply lucas_primality 4083688121 (3 : ZMod 4083688121)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (5741, 1), (17783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (5741, 1), (17783, 1)] : List FactorBlock).map factorBlockValue).prod) = 4083688121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_5741
      · exact prime_oneHundredSevenDA_17783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4083688121) ^ 2041844060 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083688121) ^ 816737624 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083688121) ^ 711320 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4083688121) ^ 229640 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4135121909 : Nat.Prime 4135121909 := by
  apply lucas_primality 4135121909 (2 : ZMod 4135121909)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (17521703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (17521703, 1)] : List FactorBlock).map factorBlockValue).prod) = 4135121909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_17521703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4135121909) ^ 2067560954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4135121909) ^ 70086812 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4135121909) ^ 236 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5278879751 : Nat.Prime 5278879751 := by
  apply lucas_primality 5278879751 (13 : ZMod 5278879751)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 3), (67, 1), (113, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 3), (67, 1), (113, 1), (2789, 1)] : List FactorBlock).map factorBlockValue).prod) = 5278879751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_67
      · exact prime_oneHundredSevenDA_113
      · exact prime_oneHundredSevenDA_2789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5278879751) ^ 2639439875 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 5278879751) ^ 1055775950 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 5278879751) ^ 78789250 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 5278879751) ^ 46715750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 5278879751) ^ 1892750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5355894617 : Nat.Prime 5355894617 := by
  apply lucas_primality 5355894617 (3 : ZMod 5355894617)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (41, 2), (398267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (41, 2), (398267, 1)] : List FactorBlock).map factorBlockValue).prod) = 5355894617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_398267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 5355894617) ^ 2677947308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5355894617) ^ 130631576 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5355894617) ^ 13448 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5385300859 : Nat.Prime 5385300859 := by
  apply lucas_primality 5385300859 (10 : ZMod 5385300859)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (5107, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (5107, 1), (8369, 1)] : List FactorBlock).map factorBlockValue).prod) = 5385300859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_5107
      · exact prime_oneHundredSevenDA_8369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 5385300859) ^ 2692650429 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5385300859) ^ 1795100286 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5385300859) ^ 769328694 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5385300859) ^ 1054494 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 5385300859) ^ 643482 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5507001827 : Nat.Prime 5507001827 := by
  apply lucas_primality 5507001827 (2 : ZMod 5507001827)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (59, 1), (71, 1), (28579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (59, 1), (71, 1), (28579, 1)] : List FactorBlock).map factorBlockValue).prod) = 5507001827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_71
      · exact prime_oneHundredSevenDA_28579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5507001827) ^ 2753500913 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5507001827) ^ 239434862 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5507001827) ^ 93339014 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5507001827) ^ 77563406 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 5507001827) ^ 192694 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5603032723 : Nat.Prime 5603032723 := by
  apply lucas_primality 5603032723 (3 : ZMod 5603032723)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (133405541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (133405541, 1)] : List FactorBlock).map factorBlockValue).prod) = 5603032723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_133405541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5603032723) ^ 2801516361 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5603032723) ^ 1867677574 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5603032723) ^ 800433246 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5603032723) ^ 42 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5858281831 : Nat.Prime 5858281831 := by
  apply lucas_primality 5858281831 (21 : ZMod 5858281831)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (12253, 1), (15937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (12253, 1), (15937, 1)] : List FactorBlock).map factorBlockValue).prod) = 5858281831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_12253
      · exact prime_oneHundredSevenDA_15937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (21 : ZMod 5858281831) ^ 2929140915 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (21 : ZMod 5858281831) ^ 1952760610 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (21 : ZMod 5858281831) ^ 1171656366 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (21 : ZMod 5858281831) ^ 478110 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (21 : ZMod 5858281831) ^ 367590 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_6077575109 : Nat.Prime 6077575109 := by
  apply lucas_primality 6077575109 (2 : ZMod 6077575109)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (23, 1), (43, 1), (139663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (23, 1), (43, 1), (139663, 1)] : List FactorBlock).map factorBlockValue).prod) = 6077575109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_139663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6077575109) ^ 3038787554 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077575109) ^ 552506828 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077575109) ^ 264242396 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077575109) ^ 141338956 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6077575109) ^ 43516 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_7430988553 : Nat.Prime 7430988553 := by
  apply lucas_primality 7430988553 (5 : ZMod 7430988553)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (23817271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (23817271, 1)] : List FactorBlock).map factorBlockValue).prod) = 7430988553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_23817271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 7430988553) ^ 3715494276 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7430988553) ^ 2476996184 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7430988553) ^ 571614504 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7430988553) ^ 312 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_7607134897 : Nat.Prime 7607134897 := by
  apply lucas_primality 7607134897 (7 : ZMod 7607134897)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (367, 1), (431831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (367, 1), (431831, 1)] : List FactorBlock).map factorBlockValue).prod) = 7607134897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_367
      · exact prime_oneHundredSevenDA_431831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 7607134897) ^ 3803567448 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 7607134897) ^ 2535711632 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 7607134897) ^ 20727888 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 7607134897) ^ 17616 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_7750939507 : Nat.Prime 7750939507 := by
  apply lucas_primality 7750939507 (11 : ZMod 7750939507)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (1129, 1), (67307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (1129, 1), (67307, 1)] : List FactorBlock).map factorBlockValue).prod) = 7750939507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_1129
      · exact prime_oneHundredSevenDA_67307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 7750939507) ^ 3875469753 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7750939507) ^ 2583646502 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7750939507) ^ 455937618 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7750939507) ^ 6865314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 7750939507) ^ 115158 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_7795194553 : Nat.Prime 7795194553 := by
  apply lucas_primality 7795194553 (5 : ZMod 7795194553)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (251, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (251, 1), (25373, 1)] : List FactorBlock).map factorBlockValue).prod) = 7795194553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_251
      · exact prime_oneHundredSevenDA_25373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 7795194553) ^ 3897597276 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 2598398184 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 458540856 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 31056552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 7795194553) ^ 307224 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_8270243819 : Nat.Prime 8270243819 := by
  apply lucas_primality 8270243819 (2 : ZMod 8270243819)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4135121909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4135121909, 1)] : List FactorBlock).map factorBlockValue).prod) = 8270243819 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_4135121909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 8270243819) ^ 4135121909 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8270243819) ^ 2 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_8611472453 : Nat.Prime 8611472453 := by
  apply lucas_primality 8611472453 (2 : ZMod 8611472453)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (195715283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (195715283, 1)] : List FactorBlock).map factorBlockValue).prod) = 8611472453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_195715283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8611472453) ^ 4305736226 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8611472453) ^ 782861132 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 8611472453) ^ 44 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_10981539931 : Nat.Prime 10981539931 := by
  apply lucas_primality 10981539931 (3 : ZMod 10981539931)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (83, 1), (151, 1), (29207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (83, 1), (151, 1), (29207, 1)] : List FactorBlock).map factorBlockValue).prod) = 10981539931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_83
      · exact prime_oneHundredSevenDA_151
      · exact prime_oneHundredSevenDA_29207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10981539931) ^ 5490769965 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10981539931) ^ 3660513310 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10981539931) ^ 2196307986 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10981539931) ^ 132307710 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10981539931) ^ 72725430 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 10981539931) ^ 375990 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_11052204403 : Nat.Prime 11052204403 := by
  apply lucas_primality 11052204403 (2 : ZMod 11052204403)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1842034067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1842034067, 1)] : List FactorBlock).map factorBlockValue).prod) = 11052204403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_1842034067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 11052204403) ^ 5526102201 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11052204403) ^ 3684068134 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 11052204403) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_12567749113 : Nat.Prime 12567749113 := by
  apply lucas_primality 12567749113 (5 : ZMod 12567749113)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (83, 1), (211, 1), (9967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (83, 1), (211, 1), (9967, 1)] : List FactorBlock).map factorBlockValue).prod) = 12567749113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_83
      · exact prime_oneHundredSevenDA_211
      · exact prime_oneHundredSevenDA_9967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 12567749113) ^ 6283874556 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12567749113) ^ 4189249704 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12567749113) ^ 151418664 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12567749113) ^ 59562792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 12567749113) ^ 1260936 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_14159503789 : Nat.Prime 14159503789 := by
  apply lucas_primality 14159503789 (2 : ZMod 14159503789)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1179958649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1179958649, 1)] : List FactorBlock).map factorBlockValue).prod) = 14159503789 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_1179958649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14159503789) ^ 7079751894 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14159503789) ^ 4719834596 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14159503789) ^ 12 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_14447351543 : Nat.Prime 14447351543 := by
  apply lucas_primality 14447351543 (5 : ZMod 14447351543)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (555667367, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (555667367, 1)] : List FactorBlock).map factorBlockValue).prod) = 14447351543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_555667367
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 14447351543) ^ 7223675771 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14447351543) ^ 1111334734 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 14447351543) ^ 26 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_15366944617 : Nat.Prime 15366944617 := by
  apply lucas_primality 15366944617 (5 : ZMod 15366944617)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (233, 1), (479, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (233, 1), (479, 1), (5737, 1)] : List FactorBlock).map factorBlockValue).prod) = 15366944617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_233
      · exact prime_oneHundredSevenDA_479
      · exact prime_oneHundredSevenDA_5737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 15366944617) ^ 7683472308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15366944617) ^ 5122314872 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15366944617) ^ 65952552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15366944617) ^ 32081304 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 15366944617) ^ 2678568 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_16072457953 : Nat.Prime 16072457953 := by
  apply lucas_primality 16072457953 (5 : ZMod 16072457953)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 1), (1063, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 1), (1063, 1), (5431, 1)] : List FactorBlock).map factorBlockValue).prod) = 16072457953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_1063
      · exact prime_oneHundredSevenDA_5431
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 16072457953) ^ 8036228976 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16072457953) ^ 5357485984 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16072457953) ^ 554222688 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16072457953) ^ 15119904 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 16072457953) ^ 2959392 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_17022905881 : Nat.Prime 17022905881 := by
  apply lucas_primality 17022905881 (19 : ZMod 17022905881)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (141857549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (141857549, 1)] : List FactorBlock).map factorBlockValue).prod) = 17022905881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_141857549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 17022905881) ^ 8511452940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (19 : ZMod 17022905881) ^ 5674301960 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (19 : ZMod 17022905881) ^ 3404581176 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (19 : ZMod 17022905881) ^ 120 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_18134393371 : Nat.Prime 18134393371 := by
  apply lucas_primality 18134393371 (2 : ZMod 18134393371)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1249, 1), (483971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1249, 1), (483971, 1)] : List FactorBlock).map factorBlockValue).prod) = 18134393371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_1249
      · exact prime_oneHundredSevenDA_483971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18134393371) ^ 9067196685 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18134393371) ^ 6044797790 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18134393371) ^ 3626878674 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18134393371) ^ 14519130 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18134393371) ^ 37470 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_18639274723 : Nat.Prime 18639274723 := by
  apply lucas_primality 18639274723 (5 : ZMod 18639274723)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3106545787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3106545787, 1)] : List FactorBlock).map factorBlockValue).prod) = 18639274723 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_3106545787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 18639274723) ^ 9319637361 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18639274723) ^ 6213091574 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 18639274723) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_19448584777 : Nat.Prime 19448584777 := by
  apply lucas_primality 19448584777 (5 : ZMod 19448584777)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (761, 1), (354953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (761, 1), (354953, 1)] : List FactorBlock).map factorBlockValue).prod) = 19448584777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_761
      · exact prime_oneHundredSevenDA_354953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 19448584777) ^ 9724292388 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19448584777) ^ 6482861592 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19448584777) ^ 25556616 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19448584777) ^ 54792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_19668481967 : Nat.Prime 19668481967 := by
  apply lucas_primality 19668481967 (5 : ZMod 19668481967)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1404891569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1404891569, 1)] : List FactorBlock).map factorBlockValue).prod) = 19668481967 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_1404891569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 19668481967) ^ 9834240983 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19668481967) ^ 2809783138 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 19668481967) ^ 14 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_21207448879 : Nat.Prime 21207448879 := by
  apply lucas_primality 21207448879 (3 : ZMod 21207448879)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (11, 1), (37, 1), (1240637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (11, 1), (37, 1), (1240637, 1)] : List FactorBlock).map factorBlockValue).prod) = 21207448879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_1240637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21207448879) ^ 10603724439 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 21207448879) ^ 7069149626 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 21207448879) ^ 3029635554 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 21207448879) ^ 1927949898 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 21207448879) ^ 573174294 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 21207448879) ^ 17094 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_21676881131 : Nat.Prime 21676881131 := by
  apply lucas_primality 21676881131 (6 : ZMod 21676881131)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (31, 1), (2203, 1), (31741, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (31, 1), (2203, 1), (31741, 1)] : List FactorBlock).map factorBlockValue).prod) = 21676881131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_2203
      · exact prime_oneHundredSevenDA_31741
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21676881131) ^ 10838440565 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 21676881131) ^ 4335376226 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 21676881131) ^ 699254230 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 21676881131) ^ 9839710 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 21676881131) ^ 682930 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_27719816629 : Nat.Prime 27719816629 := by
  apply lucas_primality 27719816629 (2 : ZMod 27719816629)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (329997817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (329997817, 1)] : List FactorBlock).map factorBlockValue).prod) = 27719816629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_329997817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 27719816629) ^ 13859908314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27719816629) ^ 9239938876 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27719816629) ^ 3959973804 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27719816629) ^ 84 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_28099061597 : Nat.Prime 28099061597 := by
  apply lucas_primality 28099061597 (2 : ZMod 28099061597)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (73, 1), (79, 1), (479, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (73, 1), (79, 1), (479, 1), (2543, 1)] : List FactorBlock).map factorBlockValue).prod) = 28099061597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_73
      · exact prime_oneHundredSevenDA_79
      · exact prime_oneHundredSevenDA_479
      · exact prime_oneHundredSevenDA_2543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28099061597) ^ 14049530798 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28099061597) ^ 384918652 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28099061597) ^ 355684324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28099061597) ^ 58661924 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28099061597) ^ 11049572 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_33284050021 : Nat.Prime 33284050021 := by
  apply lucas_primality 33284050021 (2 : ZMod 33284050021)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (13, 1), (14223953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (13, 1), (14223953, 1)] : List FactorBlock).map factorBlockValue).prod) = 33284050021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_14223953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33284050021) ^ 16642025010 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33284050021) ^ 11094683340 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33284050021) ^ 6656810004 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33284050021) ^ 2560311540 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33284050021) ^ 2340 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_33310667707 : Nat.Prime 33310667707 := by
  apply lucas_primality 33310667707 (2 : ZMod 33310667707)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (157, 1), (569, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (157, 1), (569, 1), (2143, 1)] : List FactorBlock).map factorBlockValue).prod) = 33310667707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_157
      · exact prime_oneHundredSevenDA_569
      · exact prime_oneHundredSevenDA_2143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 33310667707) ^ 16655333853 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310667707) ^ 11103555902 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310667707) ^ 1148643714 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310667707) ^ 212169858 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310667707) ^ 58542474 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 33310667707) ^ 15543942 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_33401159881 : Nat.Prime 33401159881 := by
  apply lucas_primality 33401159881 (7 : ZMod 33401159881)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (11, 1), (43, 1), (588463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (11, 1), (43, 1), (588463, 1)] : List FactorBlock).map factorBlockValue).prod) = 33401159881 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_588463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 33401159881) ^ 16700579940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 33401159881) ^ 11133719960 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 33401159881) ^ 6680231976 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 33401159881) ^ 3036469080 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 33401159881) ^ 776771160 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 33401159881) ^ 56760 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_33627948617 : Nat.Prime 33627948617 := by
  apply lucas_primality 33627948617 (3 : ZMod 33627948617)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (135596567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (135596567, 1)] : List FactorBlock).map factorBlockValue).prod) = 33627948617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_135596567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33627948617) ^ 16813974308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33627948617) ^ 1084772536 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 33627948617) ^ 248 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_35405864869 : Nat.Prime 35405864869 := by
  apply lucas_primality 35405864869 (6 : ZMod 35405864869)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (19, 2), (29, 1), (25621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (19, 2), (29, 1), (25621, 1)] : List FactorBlock).map factorBlockValue).prod) = 35405864869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_25621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 35405864869) ^ 17702932434 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 35405864869) ^ 11801954956 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 35405864869) ^ 3218714988 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 35405864869) ^ 1863466572 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 35405864869) ^ 1220891892 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 35405864869) ^ 1381908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_56643842011 : Nat.Prime 56643842011 := by
  apply lucas_primality 56643842011 (2 : ZMod 56643842011)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (2351, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (31, 1), (2351, 1), (3701, 1)] : List FactorBlock).map factorBlockValue).prod) = 56643842011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_2351
      · exact prime_oneHundredSevenDA_3701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 56643842011) ^ 28321921005 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 18881280670 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 11328768402 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 8091977430 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 1827220710 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 24093510 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 56643842011) ^ 15305010 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_60293792653 : Nat.Prime 60293792653 := by
  apply lucas_primality 60293792653 (5 : ZMod 60293792653)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 1), (264446459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 1), (264446459, 1)] : List FactorBlock).map factorBlockValue).prod) = 60293792653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_264446459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 60293792653) ^ 30146896326 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60293792653) ^ 20097930884 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60293792653) ^ 3173357508 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 60293792653) ^ 228 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_66585938077 : Nat.Prime 66585938077 := by
  apply lucas_primality 66585938077 (5 : ZMod 66585938077)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (37, 1), (7141349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (37, 1), (7141349, 1)] : List FactorBlock).map factorBlockValue).prod) = 66585938077 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_7141349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 66585938077) ^ 33292969038 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66585938077) ^ 22195312692 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66585938077) ^ 9512276868 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66585938077) ^ 1799619948 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 66585938077) ^ 9324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_72666790657 : Nat.Prime 72666790657 := by
  apply lucas_primality 72666790657 (10 : ZMod 72666790657)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (463, 1), (204359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (463, 1), (204359, 1)] : List FactorBlock).map factorBlockValue).prod) = 72666790657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_463
      · exact prime_oneHundredSevenDA_204359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 72666790657) ^ 36333395328 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 72666790657) ^ 24222263552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 72666790657) ^ 156947712 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 72666790657) ^ 355584 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_74557098893 : Nat.Prime 74557098893 := by
  apply lucas_primality 74557098893 (2 : ZMod 74557098893)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (18639274723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (18639274723, 1)] : List FactorBlock).map factorBlockValue).prod) = 74557098893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_18639274723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 74557098893) ^ 37278549446 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 74557098893) ^ 4 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_85108652303 : Nat.Prime 85108652303 := by
  apply lucas_primality 85108652303 (5 : ZMod 85108652303)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (22573, 1), (50951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (22573, 1), (50951, 1)] : List FactorBlock).map factorBlockValue).prod) = 85108652303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_22573
      · exact prime_oneHundredSevenDA_50951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 85108652303) ^ 42554326151 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85108652303) ^ 2300233846 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85108652303) ^ 3770374 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 85108652303) ^ 1670402 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_86112623741 : Nat.Prime 86112623741 := by
  apply lucas_primality 86112623741 (10 : ZMod 86112623741)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (13, 1), (30109309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (13, 1), (30109309, 1)] : List FactorBlock).map factorBlockValue).prod) = 86112623741 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_30109309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 86112623741) ^ 43056311870 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 86112623741) ^ 17222524748 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 86112623741) ^ 7828420340 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 86112623741) ^ 6624047980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 86112623741) ^ 2860 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_88378280971 : Nat.Prime 88378280971 := by
  apply lucas_primality 88378280971 (7 : ZMod 88378280971)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (29, 1), (331, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (17, 1), (29, 1), (331, 1), (2579, 1)] : List FactorBlock).map factorBlockValue).prod) = 88378280971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_331
      · exact prime_oneHundredSevenDA_2579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 88378280971) ^ 44189140485 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 29459426990 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 17675656194 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 12625468710 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 5198722410 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 3047526930 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 267003870 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 88378280971) ^ 34268430 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_89491414843 : Nat.Prime 89491414843 := by
  apply lucas_primality 89491414843 (2 : ZMod 89491414843)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (43, 1), (12846887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (43, 1), (12846887, 1)] : List FactorBlock).map factorBlockValue).prod) = 89491414843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_12846887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 89491414843) ^ 44745707421 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 89491414843) ^ 29830471614 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 89491414843) ^ 2081195694 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 89491414843) ^ 6966 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_105179506363 : Nat.Prime 105179506363 := by
  apply lucas_primality 105179506363 (3 : ZMod 105179506363)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (17, 1), (31, 1), (226283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (17, 1), (31, 1), (226283, 1)] : List FactorBlock).map factorBlockValue).prod) = 105179506363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_226283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 105179506363) ^ 52589753181 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 105179506363) ^ 35059835454 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 105179506363) ^ 15025643766 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 105179506363) ^ 6187029786 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 105179506363) ^ 3392887302 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 105179506363) ^ 464814 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_106498228087 : Nat.Prime 106498228087 := by
  apply lucas_primality 106498228087 (3 : ZMod 106498228087)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (191, 1), (10325599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (191, 1), (10325599, 1)] : List FactorBlock).map factorBlockValue).prod) = 106498228087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_191
      · exact prime_oneHundredSevenDA_10325599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 106498228087) ^ 53249114043 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 106498228087) ^ 35499409362 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 106498228087) ^ 557582346 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 106498228087) ^ 10314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_190251540313 : Nat.Prime 190251540313 := by
  apply lucas_primality 190251540313 (5 : ZMod 190251540313)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (53, 1), (617, 1), (242413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (53, 1), (617, 1), (242413, 1)] : List FactorBlock).map factorBlockValue).prod) = 190251540313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_53
      · exact prime_oneHundredSevenDA_617
      · exact prime_oneHundredSevenDA_242413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 190251540313) ^ 95125770156 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 190251540313) ^ 63417180104 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 190251540313) ^ 3589651704 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 190251540313) ^ 308349336 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 190251540313) ^ 784824 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_199891912729 : Nat.Prime 199891912729 := by
  apply lucas_primality 199891912729 (14 : ZMod 199891912729)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (811, 1), (153281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (811, 1), (153281, 1)] : List FactorBlock).map factorBlockValue).prod) = 199891912729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_67
      · exact prime_oneHundredSevenDA_811
      · exact prime_oneHundredSevenDA_153281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 199891912729) ^ 99945956364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 199891912729) ^ 66630637576 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 199891912729) ^ 2983461384 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 199891912729) ^ 246475848 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 199891912729) ^ 1304088 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_204052741127 : Nat.Prime 204052741127 := by
  apply lucas_primality 204052741127 (5 : ZMod 204052741127)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (19, 1), (5849, 1), (70621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (19, 1), (5849, 1), (70621, 1)] : List FactorBlock).map factorBlockValue).prod) = 204052741127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_5849
      · exact prime_oneHundredSevenDA_70621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 204052741127) ^ 102026370563 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 204052741127) ^ 15696364702 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 204052741127) ^ 10739617954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 204052741127) ^ 34886774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 204052741127) ^ 2889406 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_206331898307 : Nat.Prime 206331898307 := by
  apply lucas_primality 206331898307 (2 : ZMod 206331898307)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (267097, 1), (386249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (267097, 1), (386249, 1)] : List FactorBlock).map factorBlockValue).prod) = 206331898307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_267097
      · exact prime_oneHundredSevenDA_386249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 206331898307) ^ 103165949153 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 206331898307) ^ 772498 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 206331898307) ^ 534194 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_247855088219 : Nat.Prime 247855088219 := by
  apply lucas_primality 247855088219 (2 : ZMod 247855088219)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (42571, 1), (2911079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (42571, 1), (2911079, 1)] : List FactorBlock).map factorBlockValue).prod) = 247855088219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_42571
      · exact prime_oneHundredSevenDA_2911079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 247855088219) ^ 123927544109 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 247855088219) ^ 5822158 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 247855088219) ^ 85142 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_481312930591 : Nat.Prime 481312930591 := by
  apply lucas_primality 481312930591 (11 : ZMod 481312930591)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (137, 1), (2383, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (137, 1), (2383, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod) = 481312930591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_137
      · exact prime_oneHundredSevenDA_2383
      · exact prime_oneHundredSevenDA_16381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 481312930591) ^ 240656465295 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 481312930591) ^ 160437643530 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 481312930591) ^ 96262586118 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 481312930591) ^ 3513233070 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 481312930591) ^ 201977730 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 481312930591) ^ 29382390 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_578436618637 : Nat.Prime 578436618637 := by
  apply lucas_primality 578436618637 (13 : ZMod 578436618637)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5355894617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5355894617, 1)] : List FactorBlock).map factorBlockValue).prod) = 578436618637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5355894617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 578436618637) ^ 289218309318 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 578436618637) ^ 192812206212 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 578436618637) ^ 108 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_627490458743 : Nat.Prime 627490458743 := by
  apply lucas_primality 627490458743 (7 : ZMod 627490458743)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (17881, 1), (131927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (17881, 1), (131927, 1)] : List FactorBlock).map factorBlockValue).prod) = 627490458743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_17881
      · exact prime_oneHundredSevenDA_131927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 627490458743) ^ 313745229371 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 627490458743) ^ 89641494106 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 627490458743) ^ 33025813618 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 627490458743) ^ 35092582 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 627490458743) ^ 4756346 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_705965654717 : Nat.Prime 705965654717 := by
  apply lucas_primality 705965654717 (2 : ZMod 705965654717)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31, 1), (813324487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31, 1), (813324487, 1)] : List FactorBlock).map factorBlockValue).prod) = 705965654717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_813324487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 705965654717) ^ 352982827358 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 705965654717) ^ 100852236388 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 705965654717) ^ 22773085636 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 705965654717) ^ 868 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_777746406187 : Nat.Prime 777746406187 := by
  apply lucas_primality 777746406187 (3 : ZMod 777746406187)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2441, 1), (17700997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2441, 1), (17700997, 1)] : List FactorBlock).map factorBlockValue).prod) = 777746406187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_2441
      · exact prime_oneHundredSevenDA_17700997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 777746406187) ^ 388873203093 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 777746406187) ^ 259248802062 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 777746406187) ^ 318617946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 777746406187) ^ 43938 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_897574651121 : Nat.Prime 897574651121 := by
  apply lucas_primality 897574651121 (3 : ZMod 897574651121)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (59, 1), (27166303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (59, 1), (27166303, 1)] : List FactorBlock).map factorBlockValue).prod) = 897574651121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_27166303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 897574651121) ^ 448787325560 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 897574651121) ^ 179514930224 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 897574651121) ^ 128224950160 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 897574651121) ^ 15213129680 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 897574651121) ^ 33040 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_958241512687 : Nat.Prime 958241512687 := by
  apply lucas_primality 958241512687 (3 : ZMod 958241512687)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5807, 1), (27502483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5807, 1), (27502483, 1)] : List FactorBlock).map factorBlockValue).prod) = 958241512687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5807
      · exact prime_oneHundredSevenDA_27502483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 958241512687) ^ 479120756343 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 958241512687) ^ 319413837562 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 958241512687) ^ 165014898 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 958241512687) ^ 34842 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1007624474933 : Nat.Prime 1007624474933 := by
  apply lucas_primality 1007624474933 (2 : ZMod 1007624474933)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (5858281831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (5858281831, 1)] : List FactorBlock).map factorBlockValue).prod) = 1007624474933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_5858281831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1007624474933) ^ 503812237466 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007624474933) ^ 23433127324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1007624474933) ^ 172 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1142935879109 : Nat.Prime 1142935879109 := by
  apply lucas_primality 1142935879109 (2 : ZMod 1142935879109)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (181, 1), (3559, 1), (443563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (181, 1), (3559, 1), (443563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1142935879109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_181
      · exact prime_oneHundredSevenDA_3559
      · exact prime_oneHundredSevenDA_443563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1142935879109) ^ 571467939554 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1142935879109) ^ 6314562868 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1142935879109) ^ 321139612 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1142935879109) ^ 2576716 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1198546885387 : Nat.Prime 1198546885387 := by
  apply lucas_primality 1198546885387 (2 : ZMod 1198546885387)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (66585938077, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (66585938077, 1)] : List FactorBlock).map factorBlockValue).prod) = 1198546885387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_66585938077
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1198546885387) ^ 599273442693 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198546885387) ^ 399515628462 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1198546885387) ^ 18 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1274564009657 : Nat.Prime 1274564009657 := by
  apply lucas_primality 1274564009657 (3 : ZMod 1274564009657)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (151, 1), (150728951, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (151, 1), (150728951, 1)] : List FactorBlock).map factorBlockValue).prod) = 1274564009657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_151
      · exact prime_oneHundredSevenDA_150728951
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1274564009657) ^ 637282004828 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1274564009657) ^ 182080572808 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1274564009657) ^ 8440821256 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1274564009657) ^ 8456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1325320364549 : Nat.Prime 1325320364549 := by
  apply lucas_primality 1325320364549 (2 : ZMod 1325320364549)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (10939, 1), (1781699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (10939, 1), (1781699, 1)] : List FactorBlock).map factorBlockValue).prod) = 1325320364549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_10939
      · exact prime_oneHundredSevenDA_1781699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1325320364549) ^ 662660182274 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325320364549) ^ 77960021444 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325320364549) ^ 121155532 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1325320364549) ^ 743852 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1356661937221 : Nat.Prime 1356661937221 := by
  apply lucas_primality 1356661937221 (23 : ZMod 1356661937221)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (577, 1), (39187231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (577, 1), (39187231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1356661937221 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_577
      · exact prime_oneHundredSevenDA_39187231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (23 : ZMod 1356661937221) ^ 678330968610 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 1356661937221) ^ 452220645740 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 1356661937221) ^ 271332387444 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 1356661937221) ^ 2351233860 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 1356661937221) ^ 34620 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1363623198191 : Nat.Prime 1363623198191 := by
  apply lucas_primality 1363623198191 (7 : ZMod 1363623198191)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (673, 1), (969467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (673, 1), (969467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1363623198191 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_673
      · exact prime_oneHundredSevenDA_969467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1363623198191) ^ 681811599095 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1363623198191) ^ 272724639638 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1363623198191) ^ 123965745290 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1363623198191) ^ 71769642010 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1363623198191) ^ 2026186030 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 1363623198191) ^ 1406570 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1490547506621 : Nat.Prime 1490547506621 := by
  apply lucas_primality 1490547506621 (2 : ZMod 1490547506621)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2081, 1), (35813251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2081, 1), (35813251, 1)] : List FactorBlock).map factorBlockValue).prod) = 1490547506621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_2081
      · exact prime_oneHundredSevenDA_35813251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1490547506621) ^ 745273753310 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490547506621) ^ 298109501324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490547506621) ^ 716265020 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1490547506621) ^ 41620 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1576137244541 : Nat.Prime 1576137244541 := by
  apply lucas_primality 1576137244541 (11 : ZMod 1576137244541)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (137, 1), (281, 1), (2047091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (137, 1), (281, 1), (2047091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1576137244541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_137
      · exact prime_oneHundredSevenDA_281
      · exact prime_oneHundredSevenDA_2047091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1576137244541) ^ 788068622270 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1576137244541) ^ 315227448908 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1576137244541) ^ 11504651420 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1576137244541) ^ 5609029340 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 1576137244541) ^ 769940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1908071478857 : Nat.Prime 1908071478857 := by
  apply lucas_primality 1908071478857 (3 : ZMod 1908071478857)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (229, 1), (21211, 1), (49103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (229, 1), (21211, 1), (49103, 1)] : List FactorBlock).map factorBlockValue).prod) = 1908071478857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_229
      · exact prime_oneHundredSevenDA_21211
      · exact prime_oneHundredSevenDA_49103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1908071478857) ^ 954035739428 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908071478857) ^ 8332189864 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908071478857) ^ 89956696 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1908071478857) ^ 38858552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_2000044417487 : Nat.Prime 2000044417487 := by
  apply lucas_primality 2000044417487 (5 : ZMod 2000044417487)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (257, 1), (2957, 1), (1315907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (257, 1), (2957, 1), (1315907, 1)] : List FactorBlock).map factorBlockValue).prod) = 2000044417487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_257
      · exact prime_oneHundredSevenDA_2957
      · exact prime_oneHundredSevenDA_1315907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2000044417487) ^ 1000022208743 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2000044417487) ^ 7782273998 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2000044417487) ^ 676376198 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 2000044417487) ^ 1519898 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3835620841517 : Nat.Prime 3835620841517 := by
  apply lucas_primality 3835620841517 (2 : ZMod 3835620841517)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (787, 1), (1218431017, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (787, 1), (1218431017, 1)] : List FactorBlock).map factorBlockValue).prod) = 3835620841517 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_787
      · exact prime_oneHundredSevenDA_1218431017
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3835620841517) ^ 1917810420758 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3835620841517) ^ 4873724068 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3835620841517) ^ 3148 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4360294537549 : Nat.Prime 4360294537549 := by
  apply lucas_primality 4360294537549 (2 : ZMod 4360294537549)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (757, 1), (479997197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (757, 1), (479997197, 1)] : List FactorBlock).map factorBlockValue).prod) = 4360294537549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_757
      · exact prime_oneHundredSevenDA_479997197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4360294537549) ^ 2180147268774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4360294537549) ^ 1453431512516 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4360294537549) ^ 5759966364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4360294537549) ^ 9084 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5005586177051 : Nat.Prime 5005586177051 := by
  apply lucas_primality 5005586177051 (6 : ZMod 5005586177051)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (2017, 1), (49633973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (2017, 1), (49633973, 1)] : List FactorBlock).map factorBlockValue).prod) = 5005586177051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_2017
      · exact prime_oneHundredSevenDA_49633973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 5005586177051) ^ 2502793088525 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5005586177051) ^ 1001117235410 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5005586177051) ^ 2481698650 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 5005586177051) ^ 100850 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5771140790923 : Nat.Prime 5771140790923 := by
  apply lucas_primality 5771140790923 (5 : ZMod 5771140790923)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (239, 1), (103192447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (239, 1), (103192447, 1)] : List FactorBlock).map factorBlockValue).prod) = 5771140790923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_239
      · exact prime_oneHundredSevenDA_103192447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 5771140790923) ^ 2885570395461 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5771140790923) ^ 1923713596974 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5771140790923) ^ 443933906994 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5771140790923) ^ 24147032598 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 5771140790923) ^ 55926 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_7196762823751 : Nat.Prime 7196762823751 := by
  apply lucas_primality 7196762823751 (6 : ZMod 7196762823751)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 4), (3761, 1), (18899, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 4), (3761, 1), (18899, 1)] : List FactorBlock).map factorBlockValue).prod) = 7196762823751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_3761
      · exact prime_oneHundredSevenDA_18899
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7196762823751) ^ 3598381411875 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7196762823751) ^ 2398920941250 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7196762823751) ^ 1439352564750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7196762823751) ^ 1913523750 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 7196762823751) ^ 380801250 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_8354409772391 : Nat.Prime 8354409772391 := by
  apply lucas_primality 8354409772391 (7 : ZMod 8354409772391)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (67, 1), (1133569847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (67, 1), (1133569847, 1)] : List FactorBlock).map factorBlockValue).prod) = 8354409772391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_67
      · exact prime_oneHundredSevenDA_1133569847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 8354409772391) ^ 4177204886195 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8354409772391) ^ 1670881954478 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8354409772391) ^ 759491797490 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8354409772391) ^ 124692683170 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 8354409772391) ^ 7370 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_10882316342731 : Nat.Prime 10882316342731 := by
  apply lucas_primality 10882316342731 (2 : ZMod 10882316342731)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (29879, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (47, 1), (29879, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) = 10882316342731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_47
      · exact prime_oneHundredSevenDA_29879
      · exact prime_oneHundredSevenDA_36901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10882316342731) ^ 5441158171365 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 3627438780910 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 2176463268546 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 1554616620390 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 231538645590 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 364212870 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10882316342731) ^ 294905730 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_11448428873143 : Nat.Prime 11448428873143 := by
  apply lucas_primality 11448428873143 (3 : ZMod 11448428873143)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1908071478857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1908071478857, 1)] : List FactorBlock).map factorBlockValue).prod) = 11448428873143 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_1908071478857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 11448428873143) ^ 5724214436571 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11448428873143) ^ 3816142957714 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 11448428873143) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_14672339050241 : Nat.Prime 14672339050241 := by
  apply lucas_primality 14672339050241 (6 : ZMod 14672339050241)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (5, 1), (83, 1), (138105601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (5, 1), (83, 1), (138105601, 1)] : List FactorBlock).map factorBlockValue).prod) = 14672339050241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_83
      · exact prime_oneHundredSevenDA_138105601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 14672339050241) ^ 7336169525120 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14672339050241) ^ 2934467810048 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14672339050241) ^ 176775169280 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 14672339050241) ^ 106240 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_17260047911009 : Nat.Prime 17260047911009 := by
  apply lucas_primality 17260047911009 (3 : ZMod 17260047911009)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (23, 1), (5881, 1), (569659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (23, 1), (5881, 1), (569659, 1)] : List FactorBlock).map factorBlockValue).prod) = 17260047911009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_5881
      · exact prime_oneHundredSevenDA_569659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 17260047911009) ^ 8630023955504 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 17260047911009) ^ 2465721130144 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 17260047911009) ^ 750436865696 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 17260047911009) ^ 2934883168 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 17260047911009) ^ 30298912 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_17948884285411 : Nat.Prime 17948884285411 := by
  apply lucas_primality 17948884285411 (2 : ZMod 17948884285411)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (3540213863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (3540213863, 1)] : List FactorBlock).map factorBlockValue).prod) = 17948884285411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_3540213863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17948884285411) ^ 8974442142705 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17948884285411) ^ 5982961428470 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17948884285411) ^ 3589776857082 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17948884285411) ^ 1380683406570 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 17948884285411) ^ 5070 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_19865558029909 : Nat.Prime 19865558029909 := by
  apply lucas_primality 19865558029909 (2 : ZMod 19865558029909)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (103, 1), (16072457953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (103, 1), (16072457953, 1)] : List FactorBlock).map factorBlockValue).prod) = 19865558029909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_103
      · exact prime_oneHundredSevenDA_16072457953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 19865558029909) ^ 9932779014954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19865558029909) ^ 6621852676636 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19865558029909) ^ 192869495436 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19865558029909) ^ 1236 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_21812515446563 : Nat.Prime 21812515446563 := by
  apply lucas_primality 21812515446563 (2 : ZMod 21812515446563)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (1553, 1), (5503, 1), (9181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (1553, 1), (5503, 1), (9181, 1)] : List FactorBlock).map factorBlockValue).prod) = 21812515446563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_139
      · exact prime_oneHundredSevenDA_1553
      · exact prime_oneHundredSevenDA_5503
      · exact prime_oneHundredSevenDA_9181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 21812515446563) ^ 10906257723281 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21812515446563) ^ 156924571558 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21812515446563) ^ 14045405954 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21812515446563) ^ 3963749854 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 21812515446563) ^ 2375832202 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_25228147133927 : Nat.Prime 25228147133927 := by
  apply lucas_primality 25228147133927 (5 : ZMod 25228147133927)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (107, 1), (691, 1), (1303, 1), (11903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (107, 1), (691, 1), (1303, 1), (11903, 1)] : List FactorBlock).map factorBlockValue).prod) = 25228147133927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_107
      · exact prime_oneHundredSevenDA_691
      · exact prime_oneHundredSevenDA_1303
      · exact prime_oneHundredSevenDA_11903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 25228147133927) ^ 12614073566963 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25228147133927) ^ 2293467921266 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25228147133927) ^ 235777076018 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25228147133927) ^ 36509619586 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25228147133927) ^ 19361586442 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 25228147133927) ^ 2119478042 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_26678970689783 : Nat.Prime 26678970689783 := by
  apply lucas_primality 26678970689783 (5 : ZMod 26678970689783)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (37, 1), (21207448879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (37, 1), (21207448879, 1)] : List FactorBlock).map factorBlockValue).prod) = 26678970689783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_21207448879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 26678970689783) ^ 13339485344891 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26678970689783) ^ 1569351217046 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26678970689783) ^ 721053261886 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 26678970689783) ^ 1258 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_28103992226657 : Nat.Prime 28103992226657 := by
  apply lucas_primality 28103992226657 (3 : ZMod 28103992226657)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (683, 1), (2617, 1), (491353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (683, 1), (2617, 1), (491353, 1)] : List FactorBlock).map factorBlockValue).prod) = 28103992226657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_683
      · exact prime_oneHundredSevenDA_2617
      · exact prime_oneHundredSevenDA_491353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 28103992226657) ^ 14051996113328 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28103992226657) ^ 41147865632 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28103992226657) ^ 10739011168 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 28103992226657) ^ 57197152 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_34538557055857 : Nat.Prime 34538557055857 := by
  apply lucas_primality 34538557055857 (10 : ZMod 34538557055857)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 2), (29, 1), (506371057, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 2), (29, 1), (506371057, 1)] : List FactorBlock).map factorBlockValue).prod) = 34538557055857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_29
      · exact prime_oneHundredSevenDA_506371057
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 34538557055857) ^ 17269278527928 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34538557055857) ^ 11512852351952 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34538557055857) ^ 4934079579408 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34538557055857) ^ 1190984726064 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 34538557055857) ^ 68208 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_34626844745539 : Nat.Prime 34626844745539 := by
  apply lucas_primality 34626844745539 (2 : ZMod 34626844745539)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5771140790923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5771140790923, 1)] : List FactorBlock).map factorBlockValue).prod) = 34626844745539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5771140790923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 34626844745539) ^ 17313422372769 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34626844745539) ^ 11542281581846 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 34626844745539) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_43478402059133 : Nat.Prime 43478402059133 := by
  apply lucas_primality 43478402059133 (2 : ZMod 43478402059133)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (307, 1), (35405864869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (307, 1), (35405864869, 1)] : List FactorBlock).map factorBlockValue).prod) = 43478402059133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_307
      · exact prime_oneHundredSevenDA_35405864869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 43478402059133) ^ 21739201029566 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 43478402059133) ^ 141623459476 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 43478402059133) ^ 1228 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_47045376340913 : Nat.Prime 47045376340913 := by
  apply lucas_primality 47045376340913 (3 : ZMod 47045376340913)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (557, 1), (5278879751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (557, 1), (5278879751, 1)] : List FactorBlock).map factorBlockValue).prod) = 47045376340913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_557
      · exact prime_oneHundredSevenDA_5278879751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47045376340913) ^ 23522688170456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47045376340913) ^ 84462076016 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 47045376340913) ^ 8912 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_59085209125801 : Nat.Prime 59085209125801 := by
  apply lucas_primality 59085209125801 (51 : ZMod 59085209125801)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 2), (11, 1), (13, 1), (211, 1), (1087897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 2), (11, 1), (13, 1), (211, 1), (1087897, 1)] : List FactorBlock).map factorBlockValue).prod) = 59085209125801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_211
      · exact prime_oneHundredSevenDA_1087897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (51 : ZMod 59085209125801) ^ 29542604562900 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 19695069708600 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 11817041825160 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 5371382647800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 4545016086600 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 280024687800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (51 : ZMod 59085209125801) ^ 54311400 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_78730534767371 : Nat.Prime 78730534767371 := by
  apply lucas_primality 78730534767371 (2 : ZMod 78730534767371)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (11969, 1), (17778029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (11969, 1), (17778029, 1)] : List FactorBlock).map factorBlockValue).prod) = 78730534767371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_11969
      · exact prime_oneHundredSevenDA_17778029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78730534767371) ^ 39365267383685 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78730534767371) ^ 15746106953474 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78730534767371) ^ 2127852291010 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78730534767371) ^ 6577870730 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78730534767371) ^ 4428530 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_88665595148831 : Nat.Prime 88665595148831 := by
  apply lucas_primality 88665595148831 (14 : ZMod 88665595148831)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (677, 1), (10457, 1), (178921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (677, 1), (10457, 1), (178921, 1)] : List FactorBlock).map factorBlockValue).prod) = 88665595148831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_677
      · exact prime_oneHundredSevenDA_10457
      · exact prime_oneHundredSevenDA_178921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 88665595148831) ^ 44332797574415 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 88665595148831) ^ 17733119029766 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 88665595148831) ^ 12666513592690 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 88665595148831) ^ 130968382790 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 88665595148831) ^ 8479066190 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 88665595148831) ^ 495557230 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_100668479750341 : Nat.Prime 100668479750341 := by
  apply lucas_primality 100668479750341 (2 : ZMod 100668479750341)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (5903, 1), (11579, 1), (24547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (5903, 1), (11579, 1), (24547, 1)] : List FactorBlock).map factorBlockValue).prod) = 100668479750341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_5903
      · exact prime_oneHundredSevenDA_11579
      · exact prime_oneHundredSevenDA_24547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 100668479750341) ^ 50334239875170 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100668479750341) ^ 33556159916780 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100668479750341) ^ 20133695950068 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100668479750341) ^ 17053782780 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100668479750341) ^ 8694056460 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 100668479750341) ^ 4101050220 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_138507378982157 : Nat.Prime 138507378982157 := by
  apply lucas_primality 138507378982157 (2 : ZMod 138507378982157)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (34626844745539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (34626844745539, 1)] : List FactorBlock).map factorBlockValue).prod) = 138507378982157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_34626844745539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 138507378982157) ^ 69253689491078 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 138507378982157) ^ 4 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_178937037343201 : Nat.Prime 178937037343201 := by
  apply lucas_primality 178937037343201 (23 : ZMod 178937037343201)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 2), (74557098893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 2), (74557098893, 1)] : List FactorBlock).map factorBlockValue).prod) = 178937037343201 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_74557098893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (23 : ZMod 178937037343201) ^ 89468518671600 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 178937037343201) ^ 59645679114400 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 178937037343201) ^ 35787407468640 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (23 : ZMod 178937037343201) ^ 2400 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_183132370577059 : Nat.Prime 183132370577059 := by
  apply lucas_primality 183132370577059 (2 : ZMod 183132370577059)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (4360294537549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (4360294537549, 1)] : List FactorBlock).map factorBlockValue).prod) = 183132370577059 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_4360294537549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183132370577059) ^ 91566185288529 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 183132370577059) ^ 61044123525686 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 183132370577059) ^ 26161767225294 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 183132370577059) ^ 42 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_198636158423341 : Nat.Prime 198636158423341 := by
  apply lucas_primality 198636158423341 (2 : ZMod 198636158423341)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (11, 1), (19, 1), (1733, 1), (338531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (11, 1), (19, 1), (1733, 1), (338531, 1)] : List FactorBlock).map factorBlockValue).prod) = 198636158423341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_1733
      · exact prime_oneHundredSevenDA_338531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 198636158423341) ^ 99318079211670 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 66212052807780 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 39727231684668 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 18057832583940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 10454534653860 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 114619825980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 198636158423341) ^ 586759140 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_265330325519551 : Nat.Prime 265330325519551 := by
  apply lucas_primality 265330325519551 (3 : ZMod 265330325519551)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (241, 1), (2446568239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (241, 1), (2446568239, 1)] : List FactorBlock).map factorBlockValue).prod) = 265330325519551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_241
      · exact prime_oneHundredSevenDA_2446568239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 265330325519551) ^ 132665162759775 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 265330325519551) ^ 88443441839850 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 265330325519551) ^ 53066065103910 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 265330325519551) ^ 1100955707550 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 265330325519551) ^ 108450 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_306778703210569 : Nat.Prime 306778703210569 := by
  apply lucas_primality 306778703210569 (11 : ZMod 306778703210569)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (23, 1), (16339, 1), (3779359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (23, 1), (16339, 1), (3779359, 1)] : List FactorBlock).map factorBlockValue).prod) = 306778703210569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_16339
      · exact prime_oneHundredSevenDA_3779359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 306778703210569) ^ 153389351605284 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 306778703210569) ^ 102259567736856 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 306778703210569) ^ 13338204487416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 306778703210569) ^ 18775855512 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 306778703210569) ^ 81172152 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_335576918331929 : Nat.Prime 335576918331929 := by
  apply lucas_primality 335576918331929 (3 : ZMod 335576918331929)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (15013, 1), (30703877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (15013, 1), (30703877, 1)] : List FactorBlock).map factorBlockValue).prod) = 335576918331929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_15013
      · exact prime_oneHundredSevenDA_30703877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335576918331929) ^ 167788459165964 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335576918331929) ^ 47939559761704 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335576918331929) ^ 25813609102456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335576918331929) ^ 22352422456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 335576918331929) ^ 10929464 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_336509537401579 : Nat.Prime 336509537401579 := by
  apply lucas_primality 336509537401579 (2 : ZMod 336509537401579)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (4373, 1), (180637661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (4373, 1), (180637661, 1)] : List FactorBlock).map factorBlockValue).prod) = 336509537401579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_71
      · exact prime_oneHundredSevenDA_4373
      · exact prime_oneHundredSevenDA_180637661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 336509537401579) ^ 168254768700789 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 336509537401579) ^ 112169845800526 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 336509537401579) ^ 4739570949318 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 336509537401579) ^ 76951643586 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 336509537401579) ^ 1862898 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_534474965663893 : Nat.Prime 534474965663893 := by
  apply lucas_primality 534474965663893 (5 : ZMod 534474965663893)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (157, 1), (10333, 1), (831967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (157, 1), (10333, 1), (831967, 1)] : List FactorBlock).map factorBlockValue).prod) = 534474965663893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_157
      · exact prime_oneHundredSevenDA_10333
      · exact prime_oneHundredSevenDA_831967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 534474965663893) ^ 267237482831946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 534474965663893) ^ 178158321887964 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 534474965663893) ^ 48588633242172 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 534474965663893) ^ 3404299144356 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 534474965663893) ^ 51725052324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 534474965663893) ^ 642423276 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_563977533322691 : Nat.Prime 563977533322691 := by
  apply lucas_primality 563977533322691 (2 : ZMod 563977533322691)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (3988249, 1), (14140981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (3988249, 1), (14140981, 1)] : List FactorBlock).map factorBlockValue).prod) = 563977533322691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_3988249
      · exact prime_oneHundredSevenDA_14140981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 563977533322691) ^ 281988766661345 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 563977533322691) ^ 112795506664538 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 563977533322691) ^ 141409810 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 563977533322691) ^ 39882490 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_566028880201607 : Nat.Prime 566028880201607 := by
  apply lucas_primality 566028880201607 (5 : ZMod 566028880201607)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46567, 1), (6077575109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46567, 1), (6077575109, 1)] : List FactorBlock).map factorBlockValue).prod) = 566028880201607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_46567
      · exact prime_oneHundredSevenDA_6077575109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 566028880201607) ^ 283014440100803 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 566028880201607) ^ 12155150218 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 566028880201607) ^ 93134 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_639146989999633 : Nat.Prime 639146989999633 := by
  apply lucas_primality 639146989999633 (5 : ZMod 639146989999633)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (677, 1), (19668481967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (677, 1), (19668481967, 1)] : List FactorBlock).map factorBlockValue).prod) = 639146989999633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_677
      · exact prime_oneHundredSevenDA_19668481967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 639146989999633) ^ 319573494999816 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 639146989999633) ^ 213048996666544 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 639146989999633) ^ 944087134416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 639146989999633) ^ 32496 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_709324761190649 : Nat.Prime 709324761190649 := by
  apply lucas_primality 709324761190649 (3 : ZMod 709324761190649)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (88665595148831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (88665595148831, 1)] : List FactorBlock).map factorBlockValue).prod) = 709324761190649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_88665595148831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 709324761190649) ^ 354662380595324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 709324761190649) ^ 8 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_742455440424317 : Nat.Prime 742455440424317 := by
  apply lucas_primality 742455440424317 (2 : ZMod 742455440424317)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2521, 1), (48481, 1), (1518679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2521, 1), (48481, 1), (1518679, 1)] : List FactorBlock).map factorBlockValue).prod) = 742455440424317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_2521
      · exact prime_oneHundredSevenDA_48481
      · exact prime_oneHundredSevenDA_1518679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 742455440424317) ^ 371227720212158 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 742455440424317) ^ 294508306396 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 742455440424317) ^ 15314359036 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 742455440424317) ^ 488882404 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_892620236403893 : Nat.Prime 892620236403893 := by
  apply lucas_primality 892620236403893 (5 : ZMod 892620236403893)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (61, 1), (331, 1), (11052204403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (61, 1), (331, 1), (11052204403, 1)] : List FactorBlock).map factorBlockValue).prod) = 892620236403893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_61
      · exact prime_oneHundredSevenDA_331
      · exact prime_oneHundredSevenDA_11052204403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 892620236403893) ^ 446310118201946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 892620236403893) ^ 14633118629572 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 892620236403893) ^ 2696737874332 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 892620236403893) ^ 80764 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1003270245582793 : Nat.Prime 1003270245582793 := by
  apply lucas_primality 1003270245582793 (5 : ZMod 1003270245582793)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (43, 1), (88378280971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (43, 1), (88378280971, 1)] : List FactorBlock).map factorBlockValue).prod) = 1003270245582793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_88378280971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1003270245582793) ^ 501635122791396 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1003270245582793) ^ 334423415194264 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1003270245582793) ^ 91206385962072 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1003270245582793) ^ 23331866176344 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1003270245582793) ^ 11352 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1040551886602903 : Nat.Prime 1040551886602903 := by
  apply lucas_primality 1040551886602903 (5 : ZMod 1040551886602903)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (313, 1), (5039, 1), (109957231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (313, 1), (5039, 1), (109957231, 1)] : List FactorBlock).map factorBlockValue).prod) = 1040551886602903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_313
      · exact prime_oneHundredSevenDA_5039
      · exact prime_oneHundredSevenDA_109957231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1040551886602903) ^ 520275943301451 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040551886602903) ^ 346850628867634 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040551886602903) ^ 3324446922054 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040551886602903) ^ 206499679818 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1040551886602903) ^ 9463242 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1208021757004093 : Nat.Prime 1208021757004093 := by
  apply lucas_primality 1208021757004093 (2 : ZMod 1208021757004093)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (100668479750341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (100668479750341, 1)] : List FactorBlock).map factorBlockValue).prod) = 1208021757004093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_100668479750341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1208021757004093) ^ 604010878502046 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208021757004093) ^ 402673919001364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1208021757004093) ^ 12 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1299609120666811 : Nat.Prime 1299609120666811 := by
  apply lucas_primality 1299609120666811 (3 : ZMod 1299609120666811)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (509, 1), (85108652303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (509, 1), (85108652303, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299609120666811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_509
      · exact prime_oneHundredSevenDA_85108652303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1299609120666811) ^ 649804560333405 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299609120666811) ^ 433203040222270 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299609120666811) ^ 259921824133362 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299609120666811) ^ 2553259569090 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1299609120666811) ^ 15270 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1511504857872833 : Nat.Prime 1511504857872833 := by
  apply lucas_primality 1511504857872833 (3 : ZMod 1511504857872833)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (709, 1), (33310667707, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (709, 1), (33310667707, 1)] : List FactorBlock).map factorBlockValue).prod) = 1511504857872833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_709
      · exact prime_oneHundredSevenDA_33310667707
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1511504857872833) ^ 755752428936416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1511504857872833) ^ 2131882733248 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1511504857872833) ^ 45376 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1591981953117307 : Nat.Prime 1591981953117307 := by
  apply lucas_primality 1591981953117307 (2 : ZMod 1591981953117307)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (265330325519551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (265330325519551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1591981953117307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_265330325519551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1591981953117307) ^ 795990976558653 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1591981953117307) ^ 530660651039102 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1591981953117307) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1671447318048451 : Nat.Prime 1671447318048451 := by
  apply lucas_primality 1671447318048451 (2 : ZMod 1671447318048451)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (537877, 1), (6905533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (537877, 1), (6905533, 1)] : List FactorBlock).map factorBlockValue).prod) = 1671447318048451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_537877
      · exact prime_oneHundredSevenDA_6905533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1671447318048451) ^ 835723659024225 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1671447318048451) ^ 557149106016150 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1671447318048451) ^ 334289463609690 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1671447318048451) ^ 3107489850 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1671447318048451) ^ 242044650 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_2230195535636633 : Nat.Prime 2230195535636633 := by
  apply lucas_primality 2230195535636633 (6 : ZMod 2230195535636633)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (14672339050241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (14672339050241, 1)] : List FactorBlock).map factorBlockValue).prod) = 2230195535636633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_14672339050241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 2230195535636633) ^ 1115097767818316 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2230195535636633) ^ 117378712401928 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 2230195535636633) ^ 152 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_2442638552418707 : Nat.Prime 2442638552418707 := by
  apply lucas_primality 2442638552418707 (2 : ZMod 2442638552418707)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1019, 1), (1198546885387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1019, 1), (1198546885387, 1)] : List FactorBlock).map factorBlockValue).prod) = 2442638552418707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_1019
      · exact prime_oneHundredSevenDA_1198546885387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2442638552418707) ^ 1221319276209353 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2442638552418707) ^ 2397093770774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 2442638552418707) ^ 2038 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3549928011115061 : Nat.Prime 3549928011115061 := by
  apply lucas_primality 3549928011115061 (2 : ZMod 3549928011115061)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (397, 1), (4057, 1), (110203157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (397, 1), (4057, 1), (110203157, 1)] : List FactorBlock).map factorBlockValue).prod) = 3549928011115061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_397
      · exact prime_oneHundredSevenDA_4057
      · exact prime_oneHundredSevenDA_110203157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3549928011115061) ^ 1774964005557530 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3549928011115061) ^ 709985602223012 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3549928011115061) ^ 8941884158980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3549928011115061) ^ 875013066580 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3549928011115061) ^ 32212580 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4013080982331173 : Nat.Prime 4013080982331173 := by
  apply lucas_primality 4013080982331173 (2 : ZMod 4013080982331173)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1003270245582793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1003270245582793, 1)] : List FactorBlock).map factorBlockValue).prod) = 4013080982331173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_1003270245582793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 4013080982331173) ^ 2006540491165586 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4013080982331173) ^ 4 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4871077865640473 : Nat.Prime 4871077865640473 := by
  apply lucas_primality 4871077865640473 (3 : ZMod 4871077865640473)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (461, 1), (1459, 1), (905271541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (461, 1), (1459, 1), (905271541, 1)] : List FactorBlock).map factorBlockValue).prod) = 4871077865640473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_461
      · exact prime_oneHundredSevenDA_1459
      · exact prime_oneHundredSevenDA_905271541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4871077865640473) ^ 2435538932820236 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4871077865640473) ^ 10566329426552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4871077865640473) ^ 3338641443208 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 4871077865640473) ^ 5380792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_5722025430914851 : Nat.Prime 5722025430914851 := by
  apply lucas_primality 5722025430914851 (3 : ZMod 5722025430914851)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (79, 1), (947, 1), (6301, 1), (80923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (79, 1), (947, 1), (6301, 1), (80923, 1)] : List FactorBlock).map factorBlockValue).prod) = 5722025430914851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_79
      · exact prime_oneHundredSevenDA_947
      · exact prime_oneHundredSevenDA_6301
      · exact prime_oneHundredSevenDA_80923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 5722025430914851) ^ 2861012715457425 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 1907341810304950 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 1144405086182970 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 72430701657150 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 6042265502550 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 908113859850 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 5722025430914851) ^ 70709506950 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_6657342549000337 : Nat.Prime 6657342549000337 := by
  apply lucas_primality 6657342549000337 (5 : ZMod 6657342549000337)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (463, 1), (33284050021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (463, 1), (33284050021, 1)] : List FactorBlock).map factorBlockValue).prod) = 6657342549000337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_463
      · exact prime_oneHundredSevenDA_33284050021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6657342549000337) ^ 3328671274500168 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6657342549000337) ^ 2219114183000112 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6657342549000337) ^ 14378709609072 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 6657342549000337) ^ 200016 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_10103718552568829 : Nat.Prime 10103718552568829 := by
  apply lucas_primality 10103718552568829 (2 : ZMod 10103718552568829)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (59, 1), (5303, 1), (733930481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (59, 1), (5303, 1), (733930481, 1)] : List FactorBlock).map factorBlockValue).prod) = 10103718552568829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_5303
      · exact prime_oneHundredSevenDA_733930481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10103718552568829) ^ 5051859276284414 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10103718552568829) ^ 918519868415348 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10103718552568829) ^ 171249466992692 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10103718552568829) ^ 1905283528676 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 10103718552568829) ^ 13766588 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_15105280496418737 : Nat.Prime 15105280496418737 := by
  apply lucas_primality 15105280496418737 (3 : ZMod 15105280496418737)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (293, 1), (247855088219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (293, 1), (247855088219, 1)] : List FactorBlock).map factorBlockValue).prod) = 15105280496418737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_293
      · exact prime_oneHundredSevenDA_247855088219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 15105280496418737) ^ 7552640248209368 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 15105280496418737) ^ 1161944653570672 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 15105280496418737) ^ 51553858349552 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 15105280496418737) ^ 60944 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_18329376320051707 : Nat.Prime 18329376320051707 := by
  apply lucas_primality 18329376320051707 (2 : ZMod 18329376320051707)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (13, 1), (1471, 1), (7607134897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (13, 1), (1471, 1), (7607134897, 1)] : List FactorBlock).map factorBlockValue).prod) = 18329376320051707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_1471
      · exact prime_oneHundredSevenDA_7607134897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18329376320051707) ^ 9164688160025853 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18329376320051707) ^ 6109792106683902 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18329376320051707) ^ 2618482331435958 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18329376320051707) ^ 1409952024619362 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18329376320051707) ^ 12460486961286 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 18329376320051707) ^ 2409498 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_22954394238544963 : Nat.Prime 22954394238544963 := by
  apply lucas_primality 22954394238544963 (2 : ZMod 22954394238544963)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (19, 1), (53, 1), (907, 1), (29147, 1), (47903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (19, 1), (53, 1), (907, 1), (29147, 1), (47903, 1)] : List FactorBlock).map factorBlockValue).prod) = 22954394238544963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_53
      · exact prime_oneHundredSevenDA_907
      · exact prime_oneHundredSevenDA_29147
      · exact prime_oneHundredSevenDA_47903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 22954394238544963) ^ 11477197119272481 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 7651464746181654 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 1208126012554998 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 433101778085754 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 25308042159366 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 787538828646 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 22954394238544963) ^ 479184899454 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_24395326390228303 : Nat.Prime 24395326390228303 := by
  apply lucas_primality 24395326390228303 (3 : ZMod 24395326390228303)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 2), (127, 1), (7795194553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 2), (127, 1), (7795194553, 1)] : List FactorBlock).map factorBlockValue).prod) = 24395326390228303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_127
      · exact prime_oneHundredSevenDA_7795194553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24395326390228303) ^ 12197663195114151 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 8131775463409434 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 659333145681846 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 192089184175026 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 24395326390228303) ^ 3129534 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_27211533616192787 : Nat.Prime 27211533616192787 := by
  apply lucas_primality 27211533616192787 (2 : ZMod 27211533616192787)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (197, 1), (1193, 1), (8270243819, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (197, 1), (1193, 1), (8270243819, 1)] : List FactorBlock).map factorBlockValue).prod) = 27211533616192787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_197
      · exact prime_oneHundredSevenDA_1193
      · exact prime_oneHundredSevenDA_8270243819
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27211533616192787) ^ 13605766808096393 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27211533616192787) ^ 3887361945170398 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27211533616192787) ^ 138129612264938 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27211533616192787) ^ 22809332452802 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 27211533616192787) ^ 3290294 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_31624936799640913 : Nat.Prime 31624936799640913 := by
  apply lucas_primality 31624936799640913 (5 : ZMod 31624936799640913)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (7, 1), (13, 1), (5701, 1), (10103, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (7, 1), (13, 1), (5701, 1), (10103, 1), (13967, 1)] : List FactorBlock).map factorBlockValue).prod) = 31624936799640913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_5701
      · exact prime_oneHundredSevenDA_10103
      · exact prime_oneHundredSevenDA_13967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31624936799640913) ^ 15812468399820456 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 10541645599880304 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 4517848114234416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 2432687446126224 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 5547261322512 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 3130252083504 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 31624936799640913) ^ 2264261244336 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_78552224166977987 : Nat.Prime 78552224166977987 := by
  apply lucas_primality 78552224166977987 (2 : ZMod 78552224166977987)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (79, 1), (677077, 1), (23686541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (79, 1), (677077, 1), (23686541, 1)] : List FactorBlock).map factorBlockValue).prod) = 78552224166977987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_31
      · exact prime_oneHundredSevenDA_79
      · exact prime_oneHundredSevenDA_677077
      · exact prime_oneHundredSevenDA_23686541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 78552224166977987) ^ 39276112083488993 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78552224166977987) ^ 2533942715063806 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78552224166977987) ^ 994331951480734 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78552224166977987) ^ 116016677818 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 78552224166977987) ^ 3316323146 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_217064331085719109 : Nat.Prime 217064331085719109 := by
  apply lucas_primality 217064331085719109 (6 : ZMod 217064331085719109)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (15919741, 1), (1136242999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (15919741, 1), (1136242999, 1)] : List FactorBlock).map factorBlockValue).prod) = 217064331085719109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_15919741
      · exact prime_oneHundredSevenDA_1136242999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 217064331085719109) ^ 108532165542859554 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 217064331085719109) ^ 72354777028573036 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 217064331085719109) ^ 13634915988 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 217064331085719109) ^ 191036892 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_392922570065943887 : Nat.Prime 392922570065943887 := by
  apply lucas_primality 392922570065943887 (5 : ZMod 392922570065943887)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (144073, 1), (1363623198191, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (144073, 1), (1363623198191, 1)] : List FactorBlock).map factorBlockValue).prod) = 392922570065943887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_144073
      · exact prime_oneHundredSevenDA_1363623198191
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 392922570065943887) ^ 196461285032971943 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 392922570065943887) ^ 2727246396382 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 392922570065943887) ^ 288146 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_632854800736764427 : Nat.Prime 632854800736764427 := by
  apply lucas_primality 632854800736764427 (2 : ZMod 632854800736764427)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (59, 1), (198636158423341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (59, 1), (198636158423341, 1)] : List FactorBlock).map factorBlockValue).prod) = 632854800736764427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_198636158423341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 632854800736764427) ^ 316427400368382213 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 632854800736764427) ^ 210951600245588142 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 632854800736764427) ^ 10726352554860414 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 632854800736764427) ^ 3186 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_683570948773230769 : Nat.Prime 683570948773230769 := by
  apply lucas_primality 683570948773230769 (14 : ZMod 683570948773230769)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (9061667, 1), (1571571923, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (9061667, 1), (1571571923, 1)] : List FactorBlock).map factorBlockValue).prod) = 683570948773230769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_9061667
      · exact prime_oneHundredSevenDA_1571571923
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 683570948773230769) ^ 341785474386615384 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 683570948773230769) ^ 227856982924410256 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 683570948773230769) ^ 75435452304 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (14 : ZMod 683570948773230769) ^ 434960016 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_758026075667321677 : Nat.Prime 758026075667321677 := by
  apply lucas_primality 758026075667321677 (2 : ZMod 758026075667321677)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (43, 1), (383, 1), (3835620841517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (43, 1), (383, 1), (3835620841517, 1)] : List FactorBlock).map factorBlockValue).prod) = 758026075667321677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_383
      · exact prime_oneHundredSevenDA_3835620841517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 758026075667321677) ^ 379013037833660838 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 758026075667321677) ^ 252675358555773892 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 758026075667321677) ^ 17628513387612132 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 758026075667321677) ^ 1979180354222772 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 758026075667321677) ^ 197628 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_761263319592252793 : Nat.Prime 761263319592252793 := by
  apply lucas_primality 761263319592252793 (10 : ZMod 761263319592252793)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 2), (167, 1), (457, 1), (983, 1), (2876207, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 2), (167, 1), (457, 1), (983, 1), (2876207, 1)] : List FactorBlock).map factorBlockValue).prod) = 761263319592252793 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_167
      · exact prime_oneHundredSevenDA_457
      · exact prime_oneHundredSevenDA_983
      · exact prime_oneHundredSevenDA_2876207
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 761263319592252793) ^ 380631659796126396 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 253754439864084264 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 108751902798893256 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 4558462991570376 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 1665784069129656 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 774428605892424 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 761263319592252793) ^ 264676123656 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1119361681183778827 : Nat.Prime 1119361681183778827 := by
  apply lucas_primality 1119361681183778827 (2 : ZMod 1119361681183778827)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (14844367, 1), (12567749113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (14844367, 1), (12567749113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1119361681183778827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_14844367
      · exact prime_oneHundredSevenDA_12567749113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1119361681183778827) ^ 559680840591889413 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119361681183778827) ^ 373120560394592942 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119361681183778827) ^ 75406494678 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1119361681183778827) ^ 89066202 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1228777330880552729 : Nat.Prime 1228777330880552729 := by
  apply lucas_primality 1228777330880552729 (3 : ZMod 1228777330880552729)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (809, 1), (17260047911009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (809, 1), (17260047911009, 1)] : List FactorBlock).map factorBlockValue).prod) = 1228777330880552729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_809
      · exact prime_oneHundredSevenDA_17260047911009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1228777330880552729) ^ 614388665440276364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228777330880552729) ^ 111707030080050248 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228777330880552729) ^ 1518884216168792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1228777330880552729) ^ 71192 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1270650627856804477 : Nat.Prime 1270650627856804477 := by
  apply lucas_primality 1270650627856804477 (2 : ZMod 1270650627856804477)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2239, 1), (158419, 1), (17560409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2239, 1), (158419, 1), (17560409, 1)] : List FactorBlock).map factorBlockValue).prod) = 1270650627856804477 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_2239
      · exact prime_oneHundredSevenDA_158419
      · exact prime_oneHundredSevenDA_17560409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1270650627856804477) ^ 635325313928402238 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270650627856804477) ^ 423550209285601492 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270650627856804477) ^ 74744154579812028 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270650627856804477) ^ 567508096407684 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270650627856804477) ^ 8020822173204 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1270650627856804477) ^ 72358828764 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1370977171497922921 : Nat.Prime 1370977171497922921 := by
  apply lucas_primality 1370977171497922921 (17 : ZMod 1370977171497922921)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (607, 1), (1697, 1), (10039, 1), (1104811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (607, 1), (1697, 1), (10039, 1), (1104811, 1)] : List FactorBlock).map factorBlockValue).prod) = 1370977171497922921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_607
      · exact prime_oneHundredSevenDA_1697
      · exact prime_oneHundredSevenDA_10039
      · exact prime_oneHundredSevenDA_1104811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 1370977171497922921) ^ 685488585748961460 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 456992390499307640 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 274195434299584584 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 2258611485169560 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 807882835296360 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 136565113208280 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (17 : ZMod 1370977171497922921) ^ 1240915569720 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1660802867037773533 : Nat.Prime 1660802867037773533 := by
  apply lucas_primality 1660802867037773533 (5 : ZMod 1660802867037773533)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (227, 1), (521, 1), (14447351543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (227, 1), (521, 1), (14447351543, 1)] : List FactorBlock).map factorBlockValue).prod) = 1660802867037773533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_227
      · exact prime_oneHundredSevenDA_521
      · exact prime_oneHundredSevenDA_14447351543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1660802867037773533) ^ 830401433518886766 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1660802867037773533) ^ 553600955679257844 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1660802867037773533) ^ 7316312189593716 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1660802867037773533) ^ 3187721433853692 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 1660802867037773533) ^ 114955524 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1914268425497564299 : Nat.Prime 1914268425497564299 := by
  apply lucas_primality 1914268425497564299 (2 : ZMod 1914268425497564299)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1783, 1), (178937037343201, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1783, 1), (178937037343201, 1)] : List FactorBlock).map factorBlockValue).prod) = 1914268425497564299 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_1783
      · exact prime_oneHundredSevenDA_178937037343201
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1914268425497564299) ^ 957134212748782149 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914268425497564299) ^ 638089475165854766 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914268425497564299) ^ 1073622224059206 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1914268425497564299) ^ 10698 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3323393104379974291 : Nat.Prime 3323393104379974291 := by
  apply lucas_primality 3323393104379974291 (2 : ZMod 3323393104379974291)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (733, 1), (7196762823751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (733, 1), (7196762823751, 1)] : List FactorBlock).map factorBlockValue).prod) = 3323393104379974291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_733
      · exact prime_oneHundredSevenDA_7196762823751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3323393104379974291) ^ 1661696552189987145 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3323393104379974291) ^ 1107797701459991430 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3323393104379974291) ^ 664678620875994858 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3323393104379974291) ^ 474770443482853470 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3323393104379974291) ^ 4533960578963130 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3323393104379974291) ^ 461790 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_6048290292646548697 : Nat.Prime 6048290292646548697 := by
  apply lucas_primality 6048290292646548697 (10 : ZMod 6048290292646548697)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (113, 1), (2230195535636633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (113, 1), (2230195535636633, 1)] : List FactorBlock).map factorBlockValue).prod) = 6048290292646548697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_113
      · exact prime_oneHundredSevenDA_2230195535636633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 6048290292646548697) ^ 3024145146323274348 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6048290292646548697) ^ 2016096764215516232 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6048290292646548697) ^ 53524692855279192 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 6048290292646548697) ^ 2712 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_6119659470132532867 : Nat.Prime 6119659470132532867 := by
  apply lucas_primality 6119659470132532867 (2 : ZMod 6119659470132532867)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (203761, 1), (5005586177051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (203761, 1), (5005586177051, 1)] : List FactorBlock).map factorBlockValue).prod) = 6119659470132532867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_203761
      · exact prime_oneHundredSevenDA_5005586177051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6119659470132532867) ^ 3059829735066266433 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6119659470132532867) ^ 2039886490044177622 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6119659470132532867) ^ 30033517062306 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 6119659470132532867) ^ 1222566 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_27929303622433419463 : Nat.Prime 27929303622433419463 := by
  apply lucas_primality 27929303622433419463 (3 : ZMod 27929303622433419463)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (313, 1), (248683, 1), (376115557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (313, 1), (248683, 1), (376115557, 1)] : List FactorBlock).map factorBlockValue).prod) = 27929303622433419463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_53
      · exact prime_oneHundredSevenDA_313
      · exact prime_oneHundredSevenDA_248683
      · exact prime_oneHundredSevenDA_376115557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 27929303622433419463) ^ 13964651811216709731 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27929303622433419463) ^ 9309767874144473154 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27929303622433419463) ^ 526967992876102254 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27929303622433419463) ^ 89231001988605174 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27929303622433419463) ^ 112308857551314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 27929303622433419463) ^ 74257241166 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_28107634930324658629 : Nat.Prime 28107634930324658629 := by
  apply lucas_primality 28107634930324658629 (2 : ZMod 28107634930324658629)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (599, 1), (7919, 1), (22571, 1), (21877369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (599, 1), (7919, 1), (22571, 1), (21877369, 1)] : List FactorBlock).map factorBlockValue).prod) = 28107634930324658629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_599
      · exact prime_oneHundredSevenDA_7919
      · exact prime_oneHundredSevenDA_22571
      · exact prime_oneHundredSevenDA_21877369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 28107634930324658629) ^ 14053817465162329314 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28107634930324658629) ^ 9369211643441552876 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28107634930324658629) ^ 46924265326084572 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28107634930324658629) ^ 3549391959884412 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28107634930324658629) ^ 1245298610177868 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 28107634930324658629) ^ 1284781315812 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_35018112701243628479 : Nat.Prime 35018112701243628479 := by
  apply lucas_primality 35018112701243628479 (19 : ZMod 35018112701243628479)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (761263319592252793, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (761263319592252793, 1)] : List FactorBlock).map factorBlockValue).prod) = 35018112701243628479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_761263319592252793
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 35018112701243628479) ^ 17509056350621814239 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (19 : ZMod 35018112701243628479) ^ 1522526639184505586 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (19 : ZMod 35018112701243628479) ^ 46 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_36289741755879292183 : Nat.Prime 36289741755879292183 := by
  apply lucas_primality 36289741755879292183 (3 : ZMod 36289741755879292183)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6048290292646548697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6048290292646548697, 1)] : List FactorBlock).map factorBlockValue).prod) = 36289741755879292183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_6048290292646548697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 36289741755879292183) ^ 18144870877939646091 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 36289741755879292183) ^ 12096580585293097394 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 36289741755879292183) ^ 6 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_41447421546632696731 : Nat.Prime 41447421546632696731 := by
  apply lucas_primality 41447421546632696731 (2 : ZMod 41447421546632696731)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (461, 1), (22937479, 1), (130656089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (461, 1), (22937479, 1), (130656089, 1)] : List FactorBlock).map factorBlockValue).prod) = 41447421546632696731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_461
      · exact prime_oneHundredSevenDA_22937479
      · exact prime_oneHundredSevenDA_130656089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41447421546632696731) ^ 20723710773316348365 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 41447421546632696731) ^ 13815807182210898910 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 41447421546632696731) ^ 8289484309326539346 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 41447421546632696731) ^ 89907638929788930 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 41447421546632696731) ^ 1806973710870 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 41447421546632696731) ^ 317225334570 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_56971088554912962721 : Nat.Prime 56971088554912962721 := by
  apply lucas_primality 56971088554912962721 (13 : ZMod 56971088554912962721)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (211, 1), (31019, 1), (18134393371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (211, 1), (31019, 1), (18134393371, 1)] : List FactorBlock).map factorBlockValue).prod) = 56971088554912962721 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_211
      · exact prime_oneHundredSevenDA_31019
      · exact prime_oneHundredSevenDA_18134393371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 56971088554912962721) ^ 28485544277456481360 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56971088554912962721) ^ 18990362851637654240 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56971088554912962721) ^ 11394217710982592544 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56971088554912962721) ^ 270005159028023520 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56971088554912962721) ^ 1836651360614880 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 56971088554912962721) ^ 3141604320 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_65198346058591729211 : Nat.Prime 65198346058591729211 := by
  apply lucas_primality 65198346058591729211 (2 : ZMod 65198346058591729211)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (83, 1), (78552224166977987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (83, 1), (78552224166977987, 1)] : List FactorBlock).map factorBlockValue).prod) = 65198346058591729211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_83
      · exact prime_oneHundredSevenDA_78552224166977987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 65198346058591729211) ^ 32599173029295864605 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65198346058591729211) ^ 13039669211718345842 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65198346058591729211) ^ 785522241669779870 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 65198346058591729211) ^ 830 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_66079824907298709029 : Nat.Prime 66079824907298709029 := by
  apply lucas_primality 66079824907298709029 (2 : ZMod 66079824907298709029)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (41, 1), (241, 1), (8503631, 1), (196609087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (41, 1), (241, 1), (8503631, 1), (196609087, 1)] : List FactorBlock).map factorBlockValue).prod) = 66079824907298709029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_241
      · exact prime_oneHundredSevenDA_8503631
      · exact prime_oneHundredSevenDA_196609087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 66079824907298709029) ^ 33039912453649354514 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66079824907298709029) ^ 1611703046519480708 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66079824907298709029) ^ 274190144843563108 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66079824907298709029) ^ 7770777554588 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 66079824907298709029) ^ 336097511644 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_73947002246221938409 : Nat.Prime 73947002246221938409 := by
  apply lucas_primality 73947002246221938409 (37 : ZMod 73947002246221938409)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (61, 1), (1481, 1), (224569, 1), (5624849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (61, 1), (1481, 1), (224569, 1), (5624849, 1)] : List FactorBlock).map factorBlockValue).prod) = 73947002246221938409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_61
      · exact prime_oneHundredSevenDA_1481
      · exact prime_oneHundredSevenDA_224569
      · exact prime_oneHundredSevenDA_5624849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (37 : ZMod 73947002246221938409) ^ 36973501123110969204 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (37 : ZMod 73947002246221938409) ^ 24649000748740646136 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (37 : ZMod 73947002246221938409) ^ 1212245938462654728 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (37 : ZMod 73947002246221938409) ^ 49930453913721768 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (37 : ZMod 73947002246221938409) ^ 329284105313832 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (37 : ZMod 73947002246221938409) ^ 13146486642792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_93801255584292614377 : Nat.Prime 93801255584292614377 := by
  apply lucas_primality 93801255584292614377 (5 : ZMod 93801255584292614377)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (79, 1), (3359, 1), (97919, 1), (2638873, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (79, 1), (3359, 1), (97919, 1), (2638873, 1)] : List FactorBlock).map factorBlockValue).prod) = 93801255584292614377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_19
      · exact prime_oneHundredSevenDA_79
      · exact prime_oneHundredSevenDA_3359
      · exact prime_oneHundredSevenDA_97919
      · exact prime_oneHundredSevenDA_2638873
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 93801255584292614377) ^ 46900627792146307188 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 31267085194764204792 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 4936908188646979704 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 1187357665623957144 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 27925351468976664 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 957947442113304 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 93801255584292614377) ^ 35545952982312 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_103077289338138277157 : Nat.Prime 103077289338138277157 := by
  apply lucas_primality 103077289338138277157 (2 : ZMod 103077289338138277157)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (947, 1), (27211533616192787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (947, 1), (27211533616192787, 1)] : List FactorBlock).map factorBlockValue).prod) = 103077289338138277157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_947
      · exact prime_oneHundredSevenDA_27211533616192787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 103077289338138277157) ^ 51538644669069138578 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 103077289338138277157) ^ 108846134464771148 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 103077289338138277157) ^ 3788 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_250316574017045774393 : Nat.Prime 250316574017045774393 := by
  apply lucas_primality 250316574017045774393 (3 : ZMod 250316574017045774393)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (37, 1), (57727, 1), (190251540313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (37, 1), (57727, 1), (190251540313, 1)] : List FactorBlock).map factorBlockValue).prod) = 250316574017045774393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_57727
      · exact prime_oneHundredSevenDA_190251540313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 250316574017045774393) ^ 125158287008522887196 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 250316574017045774393) ^ 35759510573863682056 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 250316574017045774393) ^ 22756052183367797672 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 250316574017045774393) ^ 6765312811271507416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 250316574017045774393) ^ 4336213106813896 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 250316574017045774393) ^ 1315713784 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_421564564500754141249 : Nat.Prime 421564564500754141249 := by
  apply lucas_primality 421564564500754141249 (7 : ZMod 421564564500754141249)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (407711441, 1), (5385300859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (407711441, 1), (5385300859, 1)] : List FactorBlock).map factorBlockValue).prod) = 421564564500754141249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_407711441
      · exact prime_oneHundredSevenDA_5385300859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 421564564500754141249) ^ 210782282250377070624 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 421564564500754141249) ^ 140521521500251380416 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 421564564500754141249) ^ 1033977764928 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 421564564500754141249) ^ 78280596672 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_567354173152527744499 : Nat.Prime 567354173152527744499 := by
  apply lucas_primality 567354173152527744499 (2 : ZMod 567354173152527744499)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (433756273, 1), (72666790657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (433756273, 1), (72666790657, 1)] : List FactorBlock).map factorBlockValue).prod) = 567354173152527744499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_433756273
      · exact prime_oneHundredSevenDA_72666790657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 567354173152527744499) ^ 283677086576263872249 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 567354173152527744499) ^ 189118057717509248166 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 567354173152527744499) ^ 1308002231826 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 567354173152527744499) ^ 7807612914 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_821990547436213261493 : Nat.Prime 821990547436213261493 := by
  apply lucas_primality 821990547436213261493 (2 : ZMod 821990547436213261493)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (203942681, 1), (1007624474933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (203942681, 1), (1007624474933, 1)] : List FactorBlock).map factorBlockValue).prod) = 821990547436213261493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_203942681
      · exact prime_oneHundredSevenDA_1007624474933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 821990547436213261493) ^ 410995273718106630746 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 821990547436213261493) ^ 4030497899732 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 821990547436213261493) ^ 815770724 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_919930086137399913311 : Nat.Prime 919930086137399913311 := by
  apply lucas_primality 919930086137399913311 (7 : ZMod 919930086137399913311)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (61, 1), (27795379, 1), (7750939507, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (61, 1), (27795379, 1), (7750939507, 1)] : List FactorBlock).map factorBlockValue).prod) = 919930086137399913311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_61
      · exact prime_oneHundredSevenDA_27795379
      · exact prime_oneHundredSevenDA_7750939507
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 919930086137399913311) ^ 459965043068699956655 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 919930086137399913311) ^ 183986017227479982662 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 919930086137399913311) ^ 131418583733914273330 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 919930086137399913311) ^ 15080821084219670710 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 919930086137399913311) ^ 33096511694890 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 919930086137399913311) ^ 118686268330 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3479244391571443636217 : Nat.Prime 3479244391571443636217 := by
  apply lucas_primality 3479244391571443636217 (3 : ZMod 3479244391571443636217)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4083688121, 1), (106498228087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4083688121, 1), (106498228087, 1)] : List FactorBlock).map factorBlockValue).prod) = 3479244391571443636217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_4083688121
      · exact prime_oneHundredSevenDA_106498228087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3479244391571443636217) ^ 1739622195785721818108 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3479244391571443636217) ^ 851985824696 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 3479244391571443636217) ^ 32669504968 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_10216492930491455852617 : Nat.Prime 10216492930491455852617 := by
  apply lucas_primality 10216492930491455852617 (10 : ZMod 10216492930491455852617)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7529, 1), (998161, 1), (56643842011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7529, 1), (998161, 1), (56643842011, 1)] : List FactorBlock).map factorBlockValue).prod) = 10216492930491455852617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7529
      · exact prime_oneHundredSevenDA_998161
      · exact prime_oneHundredSevenDA_56643842011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 10216492930491455852617) ^ 5108246465245727926308 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 10216492930491455852617) ^ 3405497643497151950872 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 10216492930491455852617) ^ 1356952175653002504 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 10216492930491455852617) ^ 10235315676019656 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 10216492930491455852617) ^ 180363700056 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_20586593207212810581737 : Nat.Prime 20586593207212810581737 := by
  apply lucas_primality 20586593207212810581737 (3 : ZMod 20586593207212810581737)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1877, 1), (1370977171497922921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1877, 1), (1370977171497922921, 1)] : List FactorBlock).map factorBlockValue).prod) = 20586593207212810581737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_1877
      · exact prime_oneHundredSevenDA_1370977171497922921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20586593207212810581737) ^ 10293296603606405290868 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20586593207212810581737) ^ 10967817371983383368 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 20586593207212810581737) ^ 15016 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_34253740243026593834591 : Nat.Prime 34253740243026593834591 := by
  apply lucas_primality 34253740243026593834591 (7 : ZMod 34253740243026593834591)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5011, 1), (683570948773230769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5011, 1), (683570948773230769, 1)] : List FactorBlock).map factorBlockValue).prod) = 34253740243026593834591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_5011
      · exact prime_oneHundredSevenDA_683570948773230769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 34253740243026593834591) ^ 17126870121513296917295 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 34253740243026593834591) ^ 6850748048605318766918 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 34253740243026593834591) ^ 6835709487732307690 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 34253740243026593834591) ^ 50110 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_42854548706344546909103 : Nat.Prime 42854548706344546909103 := by
  apply lucas_primality 42854548706344546909103 (5 : ZMod 42854548706344546909103)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3744701, 1), (5722025430914851, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3744701, 1), (5722025430914851, 1)] : List FactorBlock).map factorBlockValue).prod) = 42854548706344546909103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3744701
      · exact prime_oneHundredSevenDA_5722025430914851
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 42854548706344546909103) ^ 21427274353172273454551 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 42854548706344546909103) ^ 11444050861829702 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 42854548706344546909103) ^ 7489402 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_72672046356936047446543 : Nat.Prime 72672046356936047446543 := by
  apply lucas_primality 72672046356936047446543 (3 : ZMod 72672046356936047446543)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (1043773, 1), (892620236403893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (1043773, 1), (892620236403893, 1)] : List FactorBlock).map factorBlockValue).prod) = 72672046356936047446543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_1043773
      · exact prime_oneHundredSevenDA_892620236403893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 72672046356936047446543) ^ 36336023178468023723271 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72672046356936047446543) ^ 24224015452312015815514 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72672046356936047446543) ^ 5590157412072003649734 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72672046356936047446543) ^ 69624378439503654 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 72672046356936047446543) ^ 81414294 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_101117753519867438298407 : Nat.Prime 101117753519867438298407 := by
  apply lucas_primality 101117753519867438298407 (5 : ZMod 101117753519867438298407)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (93801255584292614377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (93801255584292614377, 1)] : List FactorBlock).map factorBlockValue).prod) = 101117753519867438298407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_93801255584292614377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 101117753519867438298407) ^ 50558876759933719149203 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 101117753519867438298407) ^ 14445393359981062614058 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 101117753519867438298407) ^ 9192523047260676208946 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 101117753519867438298407) ^ 1078 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_112008242045363749148857 : Nat.Prime 112008242045363749148857 := by
  apply lucas_primality 112008242045363749148857 (5 : ZMod 112008242045363749148857)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (41, 1), (2562718481, 1), (3416729753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (41, 1), (2562718481, 1), (3416729753, 1)] : List FactorBlock).map factorBlockValue).prod) = 112008242045363749148857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_2562718481
      · exact prime_oneHundredSevenDA_3416729753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 112008242045363749148857) ^ 56004121022681874574428 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 112008242045363749148857) ^ 37336080681787916382952 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 112008242045363749148857) ^ 8616018618874134549912 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 112008242045363749148857) ^ 2731908342569847540216 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 112008242045363749148857) ^ 43706807000376 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 112008242045363749148857) ^ 32782294808952 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_219802228209181465649369 : Nat.Prime 219802228209181465649369 := by
  apply lucas_primality 219802228209181465649369 (3 : ZMod 219802228209181465649369)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (3089, 1), (1270650627856804477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (3089, 1), (1270650627856804477, 1)] : List FactorBlock).map factorBlockValue).prod) = 219802228209181465649369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_3089
      · exact prime_oneHundredSevenDA_1270650627856804477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 219802228209181465649369) ^ 109901114104590732824684 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 219802228209181465649369) ^ 31400318315597352235624 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 219802228209181465649369) ^ 71156435159981050712 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 219802228209181465649369) ^ 172984 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_431275378590770551624889 : Nat.Prime 431275378590770551624889 := by
  apply lucas_primality 431275378590770551624889 (3 : ZMod 431275378590770551624889)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (523, 1), (103077289338138277157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (523, 1), (103077289338138277157, 1)] : List FactorBlock).map factorBlockValue).prod) = 431275378590770551624889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_523
      · exact prime_oneHundredSevenDA_103077289338138277157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 431275378590770551624889) ^ 215637689295385275812444 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 431275378590770551624889) ^ 824618314705106217256 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 431275378590770551624889) ^ 4184 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_455084455488970269892781 : Nat.Prime 455084455488970269892781 := by
  apply lucas_primality 455084455488970269892781 (2 : ZMod 455084455488970269892781)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (349, 1), (65198346058591729211, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (349, 1), (65198346058591729211, 1)] : List FactorBlock).map factorBlockValue).prod) = 455084455488970269892781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_349
      · exact prime_oneHundredSevenDA_65198346058591729211
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 455084455488970269892781) ^ 227542227744485134946390 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 455084455488970269892781) ^ 91016891097794053978556 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 455084455488970269892781) ^ 1303966921171834584220 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 455084455488970269892781) ^ 6980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_515945268485973912636593 : Nat.Prime 515945268485973912636593 := by
  apply lucas_primality 515945268485973912636593 (3 : ZMod 515945268485973912636593)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (43, 1), (3264436163, 1), (5603032723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (43, 1), (3264436163, 1), (5603032723, 1)] : List FactorBlock).map factorBlockValue).prod) = 515945268485973912636593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_3264436163
      · exact prime_oneHundredSevenDA_5603032723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 515945268485973912636593) ^ 257972634242986956318296 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 515945268485973912636593) ^ 12584030938682290552112 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 515945268485973912636593) ^ 11998727174092416572944 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 515945268485973912636593) ^ 158050347050384 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 515945268485973912636593) ^ 92083215285904 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_668024991545572640275631 : Nat.Prime 668024991545572640275631 := by
  apply lucas_primality 668024991545572640275631 (11 : ZMod 668024991545572640275631)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (43, 1), (47, 1), (563, 1), (3271, 1), (17948884285411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (43, 1), (47, 1), (563, 1), (3271, 1), (17948884285411, 1)] : List FactorBlock).map factorBlockValue).prod) = 668024991545572640275631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_47
      · exact prime_oneHundredSevenDA_563
      · exact prime_oneHundredSevenDA_3271
      · exact prime_oneHundredSevenDA_17948884285411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 668024991545572640275631) ^ 334012495772786320137815 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 133604998309114528055126 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 15535464919664480006410 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 14213297692458992346290 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 1186545278056079290010 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 204226533642792002530 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (11 : ZMod 668024991545572640275631) ^ 37218190330 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_914729792103850462733401 : Nat.Prime 914729792103850462733401 := by
  apply lucas_primality 914729792103850462733401 (13 : ZMod 914729792103850462733401)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (11, 1), (103997, 1), (121357, 1), (10981539931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (11, 1), (103997, 1), (121357, 1), (10981539931, 1)] : List FactorBlock).map factorBlockValue).prod) = 914729792103850462733401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_103997
      · exact prime_oneHundredSevenDA_121357
      · exact prime_oneHundredSevenDA_10981539931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 914729792103850462733401) ^ 457364896051925231366700 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 304909930701283487577800 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 182945958420770092546680 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 83157253827622769339400 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 8795732493282022200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 7537511574147766200 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (13 : ZMod 914729792103850462733401) ^ 83297041931400 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1277016753303540240293513 : Nat.Prime 1277016753303540240293513 := by
  apply lucas_primality 1277016753303540240293513 (3 : ZMod 1277016753303540240293513)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (19309, 1), (35357963, 1), (33401159881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (19309, 1), (35357963, 1), (33401159881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1277016753303540240293513 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_19309
      · exact prime_oneHundredSevenDA_35357963
      · exact prime_oneHundredSevenDA_33401159881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1277016753303540240293513) ^ 638508376651770120146756 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1277016753303540240293513) ^ 182430964757648605756216 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1277016753303540240293513) ^ 66135830612851014568 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1277016753303540240293513) ^ 36116807783964824 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 1277016753303540240293513) ^ 38232706823752 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_1766006206709319853469339 : Nat.Prime 1766006206709319853469339 := by
  apply lucas_primality 1766006206709319853469339 (2 : ZMod 1766006206709319853469339)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1217, 1), (748343, 1), (138507378982157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1217, 1), (748343, 1), (138507378982157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1766006206709319853469339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_1217
      · exact prime_oneHundredSevenDA_748343
      · exact prime_oneHundredSevenDA_138507378982157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1766006206709319853469339) ^ 883003103354659926734669 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1766006206709319853469339) ^ 252286600958474264781334 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1766006206709319853469339) ^ 1451114385135020421914 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1766006206709319853469339) ^ 2359888723097990966 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 1766006206709319853469339) ^ 12750268034 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_14120164817390556953199653 : Nat.Prime 14120164817390556953199653 := by
  apply lucas_primality 14120164817390556953199653 (2 : ZMod 14120164817390556953199653)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (43, 1), (53, 1), (5997791, 1), (19865558029909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (43, 1), (53, 1), (5997791, 1), (19865558029909, 1)] : List FactorBlock).map factorBlockValue).prod) = 14120164817390556953199653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_53
      · exact prime_oneHundredSevenDA_5997791
      · exact prime_oneHundredSevenDA_19865558029909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14120164817390556953199653) ^ 7060082408695278476599826 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14120164817390556953199653) ^ 1086166524414658227169204 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14120164817390556953199653) ^ 328375925985826905888364 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14120164817390556953199653) ^ 266418204101708621758484 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14120164817390556953199653) ^ 2354227551008455772 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 14120164817390556953199653) ^ 710786215828 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_15476211964644237795903559 : Nat.Prime 15476211964644237795903559 := by
  apply lucas_primality 15476211964644237795903559 (6 : ZMod 15476211964644237795903559)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (41, 1), (59, 1), (126097, 1), (1208021757004093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (41, 1), (59, 1), (126097, 1), (1208021757004093, 1)] : List FactorBlock).map factorBlockValue).prod) = 15476211964644237795903559 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_41
      · exact prime_oneHundredSevenDA_59
      · exact prime_oneHundredSevenDA_126097
      · exact prime_oneHundredSevenDA_1208021757004093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 15476211964644237795903559) ^ 7738105982322118897951779 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 5158737321548079265301186 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 2210887423520605399414794 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 377468584503517995022038 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 262308677366851488066162 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 122732594468101840614 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (6 : ZMod 15476211964644237795903559) ^ 12811203006 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_19719806172876383436276803 : Nat.Prime 19719806172876383436276803 := by
  apply lucas_primality 19719806172876383436276803 (2 : ZMod 19719806172876383436276803)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (17669, 1), (89227, 1), (2615681, 1), (103956529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (17669, 1), (89227, 1), (2615681, 1), (103956529, 1)] : List FactorBlock).map factorBlockValue).prod) = 19719806172876383436276803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_17669
      · exact prime_oneHundredSevenDA_89227
      · exact prime_oneHundredSevenDA_2615681
      · exact prime_oneHundredSevenDA_103956529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19719806172876383436276803) ^ 9859903086438191718138401 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19719806172876383436276803) ^ 857382877081581888533774 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19719806172876383436276803) ^ 1116068038535083108058 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19719806172876383436276803) ^ 221007163446898174726 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19719806172876383436276803) ^ 7539071535434322242 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 19719806172876383436276803) ^ 189692810663930338 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_25244972380563160994555117 : Nat.Prime 25244972380563160994555117 := by
  apply lucas_primality 25244972380563160994555117 (3 : ZMod 25244972380563160994555117)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1361, 1), (421564564500754141249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1361, 1), (421564564500754141249, 1)] : List FactorBlock).map factorBlockValue).prod) = 25244972380563160994555117 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_1361
      · exact prime_oneHundredSevenDA_421564564500754141249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 25244972380563160994555117) ^ 12622486190281580497277558 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25244972380563160994555117) ^ 2294997489142105544959556 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25244972380563160994555117) ^ 18548840838033182214956 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (3 : ZMod 25244972380563160994555117) ^ 59884 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_30134005859695569257674057 : Nat.Prime 30134005859695569257674057 := by
  apply lucas_primality 30134005859695569257674057 (10 : ZMod 30134005859695569257674057)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (97, 1), (137, 1), (74129603, 1), (1274564009657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (97, 1), (137, 1), (74129603, 1), (1274564009657, 1)] : List FactorBlock).map factorBlockValue).prod) = 30134005859695569257674057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_97
      · exact prime_oneHundredSevenDA_137
      · exact prime_oneHundredSevenDA_74129603
      · exact prime_oneHundredSevenDA_1274564009657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 30134005859695569257674057) ^ 15067002929847784628837028 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30134005859695569257674057) ^ 10044668619898523085891352 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30134005859695569257674057) ^ 310659854223665662450248 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30134005859695569257674057) ^ 219956247151062549326088 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30134005859695569257674057) ^ 406504346983964952 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (10 : ZMod 30134005859695569257674057) ^ 23642599062408 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_40390343741699233634647411 : Nat.Prime 40390343741699233634647411 := by
  apply lucas_primality 40390343741699233634647411 (12 : ZMod 40390343741699233634647411)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (810659, 1), (1660802867037773533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (810659, 1), (1660802867037773533, 1)] : List FactorBlock).map factorBlockValue).prod) = 40390343741699233634647411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_810659
      · exact prime_oneHundredSevenDA_1660802867037773533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 40390343741699233634647411) ^ 20195171870849616817323705 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (12 : ZMod 40390343741699233634647411) ^ 13463447913899744544882470 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (12 : ZMod 40390343741699233634647411) ^ 8078068748339846726929482 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (12 : ZMod 40390343741699233634647411) ^ 49824086011133205990 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (12 : ZMod 40390343741699233634647411) ^ 24319770 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_70201196780800221833360539 : Nat.Prime 70201196780800221833360539 := by
  apply lucas_primality 70201196780800221833360539 (2 : ZMod 70201196780800221833360539)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (72672046356936047446543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (72672046356936047446543, 1)] : List FactorBlock).map factorBlockValue).prod) = 70201196780800221833360539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_23
      · exact prime_oneHundredSevenDA_72672046356936047446543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 70201196780800221833360539) ^ 35100598390400110916680269 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70201196780800221833360539) ^ 23400398926933407277786846 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70201196780800221833360539) ^ 10028742397257174547622934 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70201196780800221833360539) ^ 3052225946991313992754806 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 70201196780800221833360539) ^ 966 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_113049648435211796017619027 : Nat.Prime 113049648435211796017619027 := by
  apply lucas_primality 113049648435211796017619027 (2 : ZMod 113049648435211796017619027)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (43, 1), (101117753519867438298407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (43, 1), (101117753519867438298407, 1)] : List FactorBlock).map factorBlockValue).prod) = 113049648435211796017619027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_13
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_101117753519867438298407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 113049648435211796017619027) ^ 56524824217605898008809513 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 113049648435211796017619027) ^ 8696126802708599693663002 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 113049648435211796017619027) ^ 2629061591516553395758582 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 113049648435211796017619027) ^ 1118 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_141819009640136771013134183 : Nat.Prime 141819009640136771013134183 := by
  apply lucas_primality 141819009640136771013134183 (5 : ZMod 141819009640136771013134183)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (73, 1), (107, 1), (53161, 1), (24395326390228303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (73, 1), (107, 1), (53161, 1), (24395326390228303, 1)] : List FactorBlock).map factorBlockValue).prod) = 141819009640136771013134183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_73
      · exact prime_oneHundredSevenDA_107
      · exact prime_oneHundredSevenDA_53161
      · exact prime_oneHundredSevenDA_24395326390228303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141819009640136771013134183) ^ 70909504820068385506567091 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141819009640136771013134183) ^ 20259858520019538716162026 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141819009640136771013134183) ^ 1942726159453928370042934 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141819009640136771013134183) ^ 1325411305048007205730226 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141819009640136771013134183) ^ 2667726522077025846262 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (5 : ZMod 141819009640136771013134183) ^ 5813367994 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_399061692741331229475443821 : Nat.Prime 399061692741331229475443821 := by
  apply lucas_primality 399061692741331229475443821 (7 : ZMod 399061692741331229475443821)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (11, 1), (27719816629, 1), (21812515446563, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (11, 1), (27719816629, 1), (21812515446563, 1)] : List FactorBlock).map factorBlockValue).prod) = 399061692741331229475443821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_27719816629
      · exact prime_oneHundredSevenDA_21812515446563
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 399061692741331229475443821) ^ 199530846370665614737721910 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 399061692741331229475443821) ^ 133020564247110409825147940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 399061692741331229475443821) ^ 79812338548266245895088764 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 399061692741331229475443821) ^ 36278335703757384497767620 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 399061692741331229475443821) ^ 14396260194731580 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 399061692741331229475443821) ^ 18295078975140 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_687513894559793476868020061 : Nat.Prime 687513894559793476868020061 := by
  apply lucas_primality 687513894559793476868020061 (2 : ZMod 687513894559793476868020061)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (43, 1), (443, 1), (10037, 1), (11783, 1), (897574651121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (43, 1), (443, 1), (10037, 1), (11783, 1), (897574651121, 1)] : List FactorBlock).map factorBlockValue).prod) = 687513894559793476868020061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_17
      · exact prime_oneHundredSevenDA_43
      · exact prime_oneHundredSevenDA_443
      · exact prime_oneHundredSevenDA_10037
      · exact prime_oneHundredSevenDA_11783
      · exact prime_oneHundredSevenDA_897574651121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 687513894559793476868020061) ^ 343756947279896738434010030 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 137502778911958695373604012 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 40441993797634910404001180 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 15988695222320778531814420 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 1551950100586441257038420 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 68497947051887364438380 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 58347949975370744026820 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 687513894559793476868020061) ^ 765968483736860 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_722871751994297141392661093 : Nat.Prime 722871751994297141392661093 := by
  apply lucas_primality 722871751994297141392661093 (2 : ZMod 722871751994297141392661093)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (37, 1), (103, 1), (9103, 1), (23633, 1), (37573, 1), (838079087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (37, 1), (103, 1), (9103, 1), (23633, 1), (37573, 1), (838079087, 1)] : List FactorBlock).map factorBlockValue).prod) = 722871751994297141392661093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_37
      · exact prime_oneHundredSevenDA_103
      · exact prime_oneHundredSevenDA_9103
      · exact prime_oneHundredSevenDA_23633
      · exact prime_oneHundredSevenDA_37573
      · exact prime_oneHundredSevenDA_838079087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 722871751994297141392661093) ^ 361435875997148570696330546 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 103267393142042448770380156 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 19537074378224247064666516 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 7018172349459195547501564 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 79410277050894995209564 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 30587388481965774188324 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 19239127884233282979604 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 722871751994297141392661093) ^ 862534053417201116 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_3833410806030363628597445189 : Nat.Prime 3833410806030363628597445189 := by
  apply lucas_primality 3833410806030363628597445189 (2 : ZMod 3833410806030363628597445189)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1621, 1), (16883, 1), (35018112701243628479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1621, 1), (16883, 1), (35018112701243628479, 1)] : List FactorBlock).map factorBlockValue).prod) = 3833410806030363628597445189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_1621
      · exact prime_oneHundredSevenDA_16883
      · exact prime_oneHundredSevenDA_35018112701243628479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3833410806030363628597445189) ^ 1916705403015181814298722594 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3833410806030363628597445189) ^ 2364843186940384718443828 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3833410806030363628597445189) ^ 227057442754863687057836 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 3833410806030363628597445189) ^ 109469372 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_4362157124103517232541920387 : Nat.Prime 4362157124103517232541920387 := by
  apply lucas_primality 4362157124103517232541920387 (2 : ZMod 4362157124103517232541920387)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (93703, 1), (110933, 1), (14818663, 1), (14159503789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (93703, 1), (110933, 1), (14818663, 1), (14159503789, 1)] : List FactorBlock).map factorBlockValue).prod) = 4362157124103517232541920387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_93703
      · exact prime_oneHundredSevenDA_110933
      · exact prime_oneHundredSevenDA_14818663
      · exact prime_oneHundredSevenDA_14159503789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4362157124103517232541920387) ^ 2181078562051758616270960193 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362157124103517232541920387) ^ 46553014568407812263662 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362157124103517232541920387) ^ 39322448001077382136442 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362157124103517232541920387) ^ 294369142756233624622 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362157124103517232541920387) ^ 308072739631760074 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_63251278299500999871857845603 : Nat.Prime 63251278299500999871857845603 := by
  apply lucas_primality 63251278299500999871857845603 (2 : ZMod 63251278299500999871857845603)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (1621, 1), (16883, 1), (35018112701243628479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (1621, 1), (16883, 1), (35018112701243628479, 1)] : List FactorBlock).map factorBlockValue).prod) = 63251278299500999871857845603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_11
      · exact prime_oneHundredSevenDA_1621
      · exact prime_oneHundredSevenDA_16883
      · exact prime_oneHundredSevenDA_35018112701243628479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63251278299500999871857845603) ^ 31625639149750499935928922801 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845603) ^ 21083759433166999957285948534 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845603) ^ 5750116209045545442896167782 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845603) ^ 39019912584516347854323162 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845603) ^ 3746447805455250836454294 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845603) ^ 1806244638 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_63251278299500999871857845621 : Nat.Prime 63251278299500999871857845621 := by
  apply lucas_primality 63251278299500999871857845621 (2 : ZMod 63251278299500999871857845621)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (54377, 1), (7172189, 1), (14759873, 1), (26161969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (54377, 1), (7172189, 1), (14759873, 1), (26161969, 1)] : List FactorBlock).map factorBlockValue).prod) = 63251278299500999871857845621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_7
      · exact prime_oneHundredSevenDA_54377
      · exact prime_oneHundredSevenDA_7172189
      · exact prime_oneHundredSevenDA_14759873
      · exact prime_oneHundredSevenDA_26161969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63251278299500999871857845621) ^ 31625639149750499935928922810 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 21083759433166999957285948540 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 12650255659900199974371569124 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 9035896899928714267408263660 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 1163199115425657904479060 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 8818964238045176984580 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 4285353830585195405940 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 63251278299500999871857845621) ^ 2417680347358449964980 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_126502556599001999743715691217 : Nat.Prime 126502556599001999743715691217 := by
  apply lucas_primality 126502556599001999743715691217 (7 : ZMod 126502556599001999743715691217)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (16903, 1), (33013, 1), (80946863, 1), (19448584777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (16903, 1), (33013, 1), (80946863, 1), (19448584777, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_16903
      · exact prime_oneHundredSevenDA_33013
      · exact prime_oneHundredSevenDA_80946863
      · exact prime_oneHundredSevenDA_19448584777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 126502556599001999743715691217) ^ 63251278299500999871857845608 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 126502556599001999743715691217) ^ 42167518866333999914571897072 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 126502556599001999743715691217) ^ 7484029852629829009271472 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 126502556599001999743715691217) ^ 3831901269166752483679632 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 126502556599001999743715691217) ^ 1562785164373843613232 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (7 : ZMod 126502556599001999743715691217) ^ 6504460764086269008 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem prime_oneHundredSevenDA_126502556599001999743715691301 : Nat.Prime 126502556599001999743715691301 := by
  apply lucas_primality 126502556599001999743715691301 (2 : ZMod 126502556599001999743715691301)
  · rw [← oneHundredSevenDAFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (20483, 1), (20586593207212810581737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (20483, 1), (20586593207212810581737, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredSevenDA_2
      · exact prime_oneHundredSevenDA_3
      · exact prime_oneHundredSevenDA_5
      · exact prime_oneHundredSevenDA_20483
      · exact prime_oneHundredSevenDA_20586593207212810581737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 126502556599001999743715691301) ^ 63251278299500999871857845650 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 126502556599001999743715691301) ^ 42167518866333999914571897100 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 126502556599001999743715691301) ^ 25300511319800399948743138260 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 126502556599001999743715691301) ^ 6175977962163843174521100 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide
    · change (2 : ZMod 126502556599001999743715691301) ^ 6144900 ≠ 1
      rw [← oneHundredSevenDAFastPow_eq_pow]
      decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691200 : Nat.totient 126502556599001999743715691200 = 50127823346405986640507904000 := by
  rw [← show ((([(2, 6), (5, 2), (107, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_107, prime_oneHundredSevenDA_171401, prime_oneHundredSevenDA_714027719, prime_oneHundredSevenDA_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691201 : Nat.totient 126502556599001999743715691201 = 76248513756852213707903161728 := by
  rw [← show ((([(3, 1), (19, 1), (23, 1), (439, 1), (219802228209181465649369, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_23, prime_oneHundredSevenDA_439, prime_oneHundredSevenDA_219802228209181465649369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691202 : Nat.totient 126502556599001999743715691202 = 63174255194843406614780252928 := by
  rw [← show ((([(2, 1), (1063, 1), (3607, 1), (49158409, 1), (335576918331929, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_1063, prime_oneHundredSevenDA_3607, prime_oneHundredSevenDA_49158409, prime_oneHundredSevenDA_335576918331929]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691203 : Nat.totient 126502556599001999743715691203 = 121320177011239772765123850240 := by
  rw [← show ((([(47, 1), (103, 1), (181, 1), (283, 1), (673, 1), (758026075667321677, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_47, prime_oneHundredSevenDA_103, prime_oneHundredSevenDA_181, prime_oneHundredSevenDA_283, prime_oneHundredSevenDA_673, prime_oneHundredSevenDA_758026075667321677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691204 : Nat.totient 126502556599001999743715691204 = 38308190454731191850570620800 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (1621, 1), (16883, 1), (35018112701243628479, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_1621, prime_oneHundredSevenDA_16883, prime_oneHundredSevenDA_35018112701243628479]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691205 : Nat.totient 126502556599001999743715691205 = 85169385077519068168144204800 := by
  rw [← show ((([(5, 1), (7, 1), (61, 2), (557, 1), (3623171269, 1), (481312930591, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_61, prime_oneHundredSevenDA_557, prime_oneHundredSevenDA_3623171269, prime_oneHundredSevenDA_481312930591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691206 : Nat.totient 126502556599001999743715691206 = 63251278299500999871857845602 := by
  rw [← show ((([(2, 1), (63251278299500999871857845603, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_63251278299500999871857845603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691207 : Nat.totient 126502556599001999743715691207 = 84333510614736314749386609408 := by
  rw [← show ((([(3, 2), (55229, 1), (756296753, 1), (336509537401579, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_55229, prime_oneHundredSevenDA_756296753, prime_oneHundredSevenDA_336509537401579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691208 : Nat.totient 126502556599001999743715691208 = 63248606199534817581296648400 := by
  rw [← show ((([(2, 3), (23671, 1), (668024991545572640275631, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_23671, prime_oneHundredSevenDA_668024991545572640275631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691209 : Nat.totient 126502556599001999743715691209 = 126502556525054997495783033600 := by
  rw [← show ((([(1710719201, 1), (73947002246221938409, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_1710719201, prime_oneHundredSevenDA_73947002246221938409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691210 : Nat.totient 126502556599001999743715691210 = 30975135370922080633720135680 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (17, 1), (41, 1), (215239, 1), (28107634930324658629, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_41, prime_oneHundredSevenDA_215239, prime_oneHundredSevenDA_28107634930324658629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691211 : Nat.totient 126502556599001999743715691211 = 123083548158062523016183305888 := by
  rw [← show ((([(37, 1), (6026197, 1), (567354173152527744499, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_37, prime_oneHundredSevenDA_6026197, prime_oneHundredSevenDA_567354173152527744499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691212 : Nat.totient 126502556599001999743715691212 = 48881130993458568834851840256 := by
  rw [← show ((([(2, 2), (7, 1), (13, 1), (43, 1), (705965654717, 1), (11448428873143, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_43, prime_oneHundredSevenDA_705965654717, prime_oneHundredSevenDA_11448428873143]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691213 : Nat.totient 126502556599001999743715691213 = 84108938435797576237108555344 := by
  rw [← show ((([(3, 1), (373, 1), (113049648435211796017619027, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_373, prime_oneHundredSevenDA_113049648435211796017619027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691214 : Nat.totient 126502556599001999743715691214 = 62685341205098873805401776128 := by
  rw [← show ((([(2, 1), (197, 2), (257, 1), (60293792653, 1), (105179506363, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_197, prime_oneHundredSevenDA_257, prime_oneHundredSevenDA_60293792653, prime_oneHundredSevenDA_105179506363]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691215 : Nat.totient 126502556599001999743715691215 = 91194479647101195822569056000 := by
  rw [← show ((([(5, 1), (11, 1), (191, 1), (281, 1), (42854548706344546909103, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_191, prime_oneHundredSevenDA_281, prime_oneHundredSevenDA_42854548706344546909103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691216 : Nat.totient 126502556599001999743715691216 = 42163746441810143083070183424 := by
  rw [← show ((([(2, 4), (3, 2), (16903, 1), (33013, 1), (80946863, 1), (19448584777, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_16903, prime_oneHundredSevenDA_33013, prime_oneHundredSevenDA_80946863, prime_oneHundredSevenDA_19448584777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691217 : Nat.totient 126502556599001999743715691217 = 126502556599001999743715691216 := by
  rw [← show ((([(126502556599001999743715691217, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_126502556599001999743715691217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691218 : Nat.totient 126502556599001999743715691218 = 63137805139322390484609638400 := by
  rw [← show ((([(2, 1), (1097, 1), (1667, 1), (6397, 1), (14341, 1), (17393, 1), (21676881131, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_1097, prime_oneHundredSevenDA_1667, prime_oneHundredSevenDA_6397, prime_oneHundredSevenDA_14341, prime_oneHundredSevenDA_17393, prime_oneHundredSevenDA_21676881131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691219 : Nat.totient 126502556599001999743715691219 = 72230555342488129449323126400 := by
  rw [← show ((([(3, 1), (7, 1), (2389, 1), (2741, 1), (919930086137399913311, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_2389, prime_oneHundredSevenDA_2741, prime_oneHundredSevenDA_919930086137399913311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691220 : Nat.totient 126502556599001999743715691220 = 47280230837018277037702963200 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (73, 1), (54709, 1), (1410767, 1), (59085209125801, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_73, prime_oneHundredSevenDA_54709, prime_oneHundredSevenDA_1410767, prime_oneHundredSevenDA_59085209125801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691221 : Nat.totient 126502556599001999743715691221 = 126063132581171515239550010880 := by
  rw [← show ((([(313, 1), (5077, 1), (12107, 1), (10478621, 1), (627490458743, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_313, prime_oneHundredSevenDA_5077, prime_oneHundredSevenDA_12107, prime_oneHundredSevenDA_10478621, prime_oneHundredSevenDA_627490458743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691222 : Nat.totient 126502556599001999743715691222 = 42167182039340788927033397568 := by
  rw [← show ((([(2, 1), (3, 1), (125219, 1), (548848667, 1), (306778703210569, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_125219, prime_oneHundredSevenDA_548848667, prime_oneHundredSevenDA_306778703210569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691223 : Nat.totient 126502556599001999743715691223 = 122140399474898482511173770808 := by
  rw [← show ((([(29, 1), (4362157124103517232541920387, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_29, prime_oneHundredSevenDA_4362157124103517232541920387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691224 : Nat.totient 126502556599001999743715691224 = 60501222721261825964385765280 := by
  rw [← show ((([(2, 3), (23, 1), (687513894559793476868020061, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_23, prime_oneHundredSevenDA_687513894559793476868020061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691225 : Nat.totient 126502556599001999743715691225 = 60124322895725939690391552000 := by
  rw [← show ((([(3, 3), (5, 2), (13, 1), (53, 1), (79, 1), (419, 1), (991, 1), (96293, 1), (86112623741, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_53, prime_oneHundredSevenDA_79, prime_oneHundredSevenDA_419, prime_oneHundredSevenDA_991, prime_oneHundredSevenDA_96293, prime_oneHundredSevenDA_86112623741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691226 : Nat.totient 126502556599001999743715691226 = 49201465781328040050864364800 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (947, 1), (1483, 1), (441333181, 1), (1325320364549, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_947, prime_oneHundredSevenDA_1483, prime_oneHundredSevenDA_441333181, prime_oneHundredSevenDA_1325320364549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691227 : Nat.totient 126502556599001999743715691227 = 115220544909906944738109160320 := by
  rw [← show ((([(17, 2), (31, 1), (14120164817390556953199653, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_31, prime_oneHundredSevenDA_14120164817390556953199653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691228 : Nat.totient 126502556599001999743715691228 = 42167070833365818459574925184 := by
  rw [← show ((([(2, 2), (3, 1), (94117, 1), (112008242045363749148857, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_94117, prime_oneHundredSevenDA_112008242045363749148857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691229 : Nat.totient 126502556599001999743715691229 = 126449180787299042198456366656 := by
  rw [← show ((([(2543, 1), (62213, 1), (79139, 1), (10103718552568829, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2543, prime_oneHundredSevenDA_62213, prime_oneHundredSevenDA_79139, prime_oneHundredSevenDA_10103718552568829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691230 : Nat.totient 126502556599001999743715691230 = 50600981773629077931657913152 := by
  rw [← show ((([(2, 1), (5, 1), (1238219, 1), (10216492930491455852617, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_1238219, prime_oneHundredSevenDA_10216492930491455852617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691231 : Nat.totient 126502556599001999743715691231 = 84335037732664606478213429400 := by
  rw [← show ((([(3, 1), (25228147133927, 1), (1671447318048451, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_25228147133927, prime_oneHundredSevenDA_1671447318048451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691232 : Nat.totient 126502556599001999743715691232 = 63251265147652240892368712832 := by
  rw [← show ((([(2, 5), (4809307, 1), (821990547436213261493, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_4809307, prime_oneHundredSevenDA_821990547436213261493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691233 : Nat.totient 126502556599001999743715691233 = 107487753800263134815005632000 := by
  rw [← show ((([(7, 1), (199, 1), (271, 1), (4138747, 1), (58086601, 1), (1393907813, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_199, prime_oneHundredSevenDA_271, prime_oneHundredSevenDA_4138747, prime_oneHundredSevenDA_58086601, prime_oneHundredSevenDA_1393907813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691234 : Nat.totient 126502556599001999743715691234 = 41452814729120607379920268608 := by
  rw [← show ((([(2, 1), (3, 2), (59, 1), (96939683, 1), (1228777330880552729, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_59, prime_oneHundredSevenDA_96939683, prime_oneHundredSevenDA_1228777330880552729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691235 : Nat.totient 126502556599001999743715691235 = 101201994295603779902467673088 := by
  rw [← show ((([(5, 1), (3638753, 1), (4367557, 1), (1591981953117307, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_3638753, prime_oneHundredSevenDA_4367557, prime_oneHundredSevenDA_1591981953117307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691236 : Nat.totient 126502556599001999743715691236 = 62967640280220726329831576808 := by
  rw [← show ((([(2, 2), (223, 1), (141819009640136771013134183, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_223, prime_oneHundredSevenDA_141819009640136771013134183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691237 : Nat.totient 126502556599001999743715691237 = 76668216120607272571948903760 := by
  rw [← show ((([(3, 1), (11, 1), (3833410806030363628597445189, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_3833410806030363628597445189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691238 : Nat.totient 126502556599001999743715691238 = 57563460207525361004276995200 := by
  rw [← show ((([(2, 1), (13, 1), (71, 1), (1576137244541, 1), (43478402059133, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_71, prime_oneHundredSevenDA_1576137244541, prime_oneHundredSevenDA_43478402059133]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691239 : Nat.totient 126502556599001999743715691239 = 119011921079827562189431896960 := by
  rw [← show ((([(19, 1), (149, 1), (4211, 1), (10197893, 1), (1040551886602903, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_149, prime_oneHundredSevenDA_4211, prime_oneHundredSevenDA_10197893, prime_oneHundredSevenDA_1040551886602903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691240 : Nat.totient 126502556599001999743715691240 = 28914331235965123718037897216 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (7, 1), (54377, 1), (7172189, 1), (14759873, 1), (26161969, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_54377, prime_oneHundredSevenDA_7172189, prime_oneHundredSevenDA_14759873, prime_oneHundredSevenDA_26161969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691241 : Nat.totient 126502556599001999743715691241 = 126403361517878802677658746880 := by
  rw [← show ((([(1423, 1), (12289, 1), (12826733, 1), (563977533322691, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_1423, prime_oneHundredSevenDA_12289, prime_oneHundredSevenDA_12826733, prime_oneHundredSevenDA_563977533322691]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691242 : Nat.totient 126502556599001999743715691242 = 63251278299500999871857845620 := by
  rw [← show ((([(2, 1), (63251278299500999871857845621, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_63251278299500999871857845621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691243 : Nat.totient 126502556599001999743715691243 = 84334620121859516175917657712 := by
  rw [← show ((([(3, 2), (201947, 1), (89491414843, 1), (777746406187, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_201947, prime_oneHundredSevenDA_89491414843, prime_oneHundredSevenDA_777746406187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691244 : Nat.totient 126502556599001999743715691244 = 59530601751035723345299046400 := by
  rw [← show ((([(2, 2), (17, 1), (5276833, 1), (32396321, 1), (10882316342731, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_5276833, prime_oneHundredSevenDA_32396321, prime_oneHundredSevenDA_10882316342731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691245 : Nat.totient 126502556599001999743715691245 = 101123166054510094261227440656 := by
  rw [← show ((([(5, 1), (1283, 1), (19719806172876383436276803, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_1283, prime_oneHundredSevenDA_19719806172876383436276803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691246 : Nat.totient 126502556599001999743715691246 = 41807268917443384211610280800 := by
  rw [← show ((([(2, 1), (3, 1), (131, 1), (1091, 1), (8048303, 1), (18329376320051707, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_131, prime_oneHundredSevenDA_1091, prime_oneHundredSevenDA_8048303, prime_oneHundredSevenDA_18329376320051707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691247 : Nat.totient 126502556599001999743715691247 = 103716381793920129894022691328 := by
  rw [← show ((([(7, 2), (23, 1), (7430988553, 1), (15105280496418737, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_23, prime_oneHundredSevenDA_7430988553, prime_oneHundredSevenDA_15105280496418737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691248 : Nat.totient 126502556599001999743715691248 = 55947076628551252957908627840 := by
  rw [← show ((([(2, 4), (11, 2), (37, 1), (1766006206709319853469339, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_37, prime_oneHundredSevenDA_1766006206709319853469339]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691249 : Nat.totient 126502556599001999743715691249 = 83736171780127867299312000000 := by
  rw [← show ((([(3, 1), (163, 1), (1061, 1), (34061, 1), (5276501, 1), (1356661937221, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_163, prime_oneHundredSevenDA_1061, prime_oneHundredSevenDA_34061, prime_oneHundredSevenDA_5276501, prime_oneHundredSevenDA_1356661937221]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691250 : Nat.totient 126502556599001999743715691250 = 49524405120316030785964400000 := by
  rw [← show ((([(2, 1), (5, 4), (47, 1), (3035612351, 1), (709324761190649, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_47, prime_oneHundredSevenDA_3035612351, prime_oneHundredSevenDA_709324761190649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691251 : Nat.totient 126502556599001999743715691251 = 113606167464950603192013265920 := by
  rw [← show ((([(13, 1), (41, 1), (359, 1), (578436618637, 1), (1142935879109, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_41, prime_oneHundredSevenDA_359, prime_oneHundredSevenDA_578436618637, prime_oneHundredSevenDA_1142935879109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691252 : Nat.totient 126502556599001999743715691252 = 40713466491632827503724589280 := by
  rw [← show ((([(2, 2), (3, 3), (29, 1), (40390343741699233634647411, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_29, prime_oneHundredSevenDA_40390343741699233634647411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691253 : Nat.totient 126502556599001999743715691253 = 126502556557554578194030873260 := by
  rw [← show ((([(3052121263, 1), (41447421546632696731, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3052121263, prime_oneHundredSevenDA_41447421546632696731]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691254 : Nat.totient 126502556599001999743715691254 = 54215379897672841501958348352 := by
  rw [← show ((([(2, 1), (7, 1), (36097877, 1), (250316574017045774393, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_36097877, prime_oneHundredSevenDA_250316574017045774393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691255 : Nat.totient 126502556599001999743715691255 = 65010987814149548504640921600 := by
  rw [← show ((([(3, 1), (5, 1), (43, 1), (101, 1), (277, 1), (10968259, 1), (639146989999633, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_43, prime_oneHundredSevenDA_101, prime_oneHundredSevenDA_277, prime_oneHundredSevenDA_10968259, prime_oneHundredSevenDA_639146989999633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691256 : Nat.totient 126502556599001999743715691256 = 63249457961679043990778135520 := by
  rw [← show ((([(2, 3), (34747, 1), (455084455488970269892781, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_34747, prime_oneHundredSevenDA_455084455488970269892781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691257 : Nat.totient 126502556599001999743715691257 = 126103494906260668514240247120 := by
  rw [← show ((([(317, 1), (399061692741331229475443821, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_317, prime_oneHundredSevenDA_399061692741331229475443821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691258 : Nat.totient 126502556599001999743715691258 = 38193747527998640051900081280 := by
  rw [← show ((([(2, 1), (3, 1), (19, 1), (31, 1), (83, 1), (431275378590770551624889, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_31, prime_oneHundredSevenDA_83, prime_oneHundredSevenDA_431275378590770551624889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691259 : Nat.totient 126502556599001999743715691259 = 113343459322659867553738752000 := by
  rw [← show ((([(11, 1), (97, 1), (241, 1), (112799, 1), (256199863, 1), (17022905881, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_97, prime_oneHundredSevenDA_241, prime_oneHundredSevenDA_112799, prime_oneHundredSevenDA_256199863, prime_oneHundredSevenDA_17022905881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691260 : Nat.totient 126502556599001999743715691260 = 50601022639599058530065213184 := by
  rw [← show ((([(2, 2), (5, 1), (34538557055857, 1), (183132370577059, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_34538557055857, prime_oneHundredSevenDA_183132370577059]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691261 : Nat.totient 126502556599001999743715691261 = 68034950361013525525987997184 := by
  rw [← show ((([(3, 2), (7, 1), (17, 1), (1787479, 1), (66079824907298709029, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_1787479, prime_oneHundredSevenDA_66079824907298709029]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691262 : Nat.totient 126502556599001999743715691262 = 63251278299469372935013787232 := by
  rw [← show ((([(2, 1), (2000044417487, 1), (31624936799640913, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_2000044417487, prime_oneHundredSevenDA_31624936799640913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691263 : Nat.totient 126502556599001999743715691263 = 125985911367155767869427200000 := by
  rw [← show ((([(269, 1), (3251, 1), (16831, 1), (1028737, 1), (8354409772391, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_269, prime_oneHundredSevenDA_3251, prime_oneHundredSevenDA_16831, prime_oneHundredSevenDA_1028737, prime_oneHundredSevenDA_8354409772391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691264 : Nat.totient 126502556599001999743715691264 = 38923844769329799975334170624 := by
  rw [← show ((([(2, 8), (3, 1), (13, 1), (2070463, 1), (6119659470132532867, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_2070463, prime_oneHundredSevenDA_6119659470132532867]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691265 : Nat.totient 126502556599001999743715691265 = 100596045007575530180163557824 := by
  rw [← show ((([(5, 1), (167, 1), (204052741127, 1), (742455440424317, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_167, prime_oneHundredSevenDA_204052741127, prime_oneHundredSevenDA_742455440424317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691266 : Nat.totient 126502556599001999743715691266 = 61285799379991181671778089680 := by
  rw [← show ((([(2, 1), (61, 1), (67, 1), (15476211964644237795903559, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_61, prime_oneHundredSevenDA_67, prime_oneHundredSevenDA_15476211964644237795903559]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691267 : Nat.totient 126502556599001999743715691267 = 83938081323360366589990736640 := by
  rw [← show ((([(3, 1), (233, 1), (2399, 1), (958183477, 1), (78730534767371, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_233, prime_oneHundredSevenDA_2399, prime_oneHundredSevenDA_958183477, prime_oneHundredSevenDA_78730534767371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691268 : Nat.totient 126502556599001999743715691268 = 54119229001566817188103534080 := by
  rw [← show ((([(2, 2), (7, 1), (983, 1), (1321, 1), (3479244391571443636217, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_983, prime_oneHundredSevenDA_1321, prime_oneHundredSevenDA_3479244391571443636217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691269 : Nat.totient 126502556599001999743715691269 = 124128183582337051029806784000 := by
  rw [← show ((([(89, 1), (151, 1), (997, 1), (7264813, 1), (1299609120666811, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_89, prime_oneHundredSevenDA_151, prime_oneHundredSevenDA_997, prime_oneHundredSevenDA_7264813, prime_oneHundredSevenDA_1299609120666811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691270 : Nat.totient 126502556599001999743715691270 = 29333926149140893517769312000 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (11, 1), (23, 1), (1565008591, 1), (3549928011115061, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_23, prime_oneHundredSevenDA_1565008591, prime_oneHundredSevenDA_3549928011115061]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691271 : Nat.totient 126502556599001999743715691271 = 126498683524687060396745718840 := by
  rw [← show ((([(32771, 1), (9824323, 1), (392922570065943887, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_32771, prime_oneHundredSevenDA_9824323, prime_oneHundredSevenDA_392922570065943887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691272 : Nat.totient 126502556599001999743715691272 = 62885663203949521543481676864 := by
  rw [← show ((([(2, 3), (173, 1), (81656879, 1), (1119361681183778827, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_173, prime_oneHundredSevenDA_81656879, prime_oneHundredSevenDA_1119361681183778827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691273 : Nat.totient 126502556599001999743715691273 = 83289133557043932354514790976 := by
  rw [← show ((([(3, 1), (109, 1), (307, 1), (54896839, 1), (22954394238544963, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_109, prime_oneHundredSevenDA_307, prime_oneHundredSevenDA_54896839, prime_oneHundredSevenDA_22954394238544963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691274 : Nat.totient 126502556599001999743715691274 = 63232243907521382530985977312 := by
  rw [← show ((([(2, 1), (3323, 1), (33627948617, 1), (566028880201607, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3323, prime_oneHundredSevenDA_33627948617, prime_oneHundredSevenDA_566028880201607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691275 : Nat.totient 126502556599001999743715691275 = 86744610239315656967119331040 := by
  rw [← show ((([(5, 2), (7, 1), (722871751994297141392661093, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_722871751994297141392661093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691276 : Nat.totient 126502556599001999743715691276 = 42167518858676926190553632592 := by
  rw [← show ((([(2, 2), (3, 1), (5507001827, 1), (1914268425497564299, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5507001827, prime_oneHundredSevenDA_1914268425497564299]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691277 : Nat.totient 126502556599001999743715691277 = 110625717511562208551308924992 := by
  rw [← show ((([(13, 1), (19, 1), (958241512687, 1), (534474965663893, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_958241512687, prime_oneHundredSevenDA_534474965663893]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691278 : Nat.totient 126502556599001999743715691278 = 58407395721625784565355967616 := by
  rw [← show ((([(2, 1), (17, 1), (53, 1), (70201196780800221833360539, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_53, prime_oneHundredSevenDA_70201196780800221833360539]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691279 : Nat.totient 126502556599001999743715691279 = 84335037553204772167248997680 := by
  rw [← show ((([(3, 4), (469929349, 1), (3323393104379974291, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_469929349, prime_oneHundredSevenDA_3323393104379974291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691280 : Nat.totient 126502556599001999743715691280 = 50601021745863083977805099904 := by
  rw [← show ((([(2, 4), (5, 1), (56617307, 1), (27929303622433419463, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_56617307, prime_oneHundredSevenDA_27929303622433419463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691281 : Nat.totient 126502556599001999743715691281 = 111036710843457461450761228800 := by
  rw [← show ((([(11, 1), (29, 1), (6960719, 1), (56971088554912962721, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_29, prime_oneHundredSevenDA_6960719, prime_oneHundredSevenDA_56971088554912962721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691282 : Nat.totient 126502556599001999743715691282 = 36143176554831940750505984400 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (87931, 1), (34253740243026593834591, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_87931, prime_oneHundredSevenDA_34253740243026593834591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691283 : Nat.totient 126502556599001999743715691283 = 126502556598369144743087014128 := by
  rw [← show ((([(199891912729, 1), (632854800736764427, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_199891912729, prime_oneHundredSevenDA_632854800736764427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691284 : Nat.totient 126502556599001999743715691284 = 63208591985794321683670104576 := by
  rw [← show ((([(2, 2), (1489, 1), (352549, 1), (2258167, 1), (26678970689783, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_1489, prime_oneHundredSevenDA_352549, prime_oneHundredSevenDA_2258167, prime_oneHundredSevenDA_26678970689783]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691285 : Nat.totient 126502556599001999743715691285 = 65621107271000096074758131712 := by
  rw [← show ((([(3, 1), (5, 1), (37, 1), (2819, 1), (372497, 1), (217064331085719109, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_37, prime_oneHundredSevenDA_2819, prime_oneHundredSevenDA_372497, prime_oneHundredSevenDA_217064331085719109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691286 : Nat.totient 126502556599001999743715691286 = 63221144293641304302600169488 := by
  rw [← show ((([(2, 1), (2099, 1), (30134005859695569257674057, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_2099, prime_oneHundredSevenDA_30134005859695569257674057]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691287 : Nat.totient 126502556599001999743715691287 = 126477311626621436582721131160 := by
  rw [← show ((([(5011, 1), (25244972380563160994555117, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5011, prime_oneHundredSevenDA_25244972380563160994555117]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691288 : Nat.totient 126502556599001999743715691288 = 42116303548583557762307097600 := by
  rw [← show ((([(2, 3), (3, 2), (919, 1), (7901, 1), (8611472453, 1), (28099061597, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_919, prime_oneHundredSevenDA_7901, prime_oneHundredSevenDA_8611472453, prime_oneHundredSevenDA_28099061597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691289 : Nat.totient 126502556599001999743715691289 = 104788659063485871991248399360 := by
  rw [← show ((([(7, 1), (31, 1), (727, 1), (530512487, 1), (1511504857872833, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_31, prime_oneHundredSevenDA_727, prime_oneHundredSevenDA_530512487, prime_oneHundredSevenDA_1511504857872833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691290 : Nat.totient 126502556599001999743715691290 = 46708636279668868497469621248 := by
  rw [← show ((([(2, 1), (5, 1), (13, 2), (15366944617, 1), (4871077865640473, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_13, prime_oneHundredSevenDA_15366944617, prime_oneHundredSevenDA_4871077865640473]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691291 : Nat.totient 126502556599001999743715691291 = 84334747849751194257977921664 := by
  rw [← show ((([(3, 1), (294923, 1), (21476747, 1), (6657342549000337, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_294923, prime_oneHundredSevenDA_21476747, prime_oneHundredSevenDA_6657342549000337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691292 : Nat.totient 126502556599001999743715691292 = 56098694722356736557469952000 := by
  rw [← show ((([(2, 2), (11, 1), (41, 1), (1490547506621, 1), (47045376340913, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_11, prime_oneHundredSevenDA_41, prime_oneHundredSevenDA_1490547506621, prime_oneHundredSevenDA_47045376340913]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691293 : Nat.totient 126502556599001999743715691293 = 117322083159502848956245534464 := by
  rw [← show ((([(23, 1), (59, 1), (73, 1), (1277016753303540240293513, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_23, prime_oneHundredSevenDA_59, prime_oneHundredSevenDA_73, prime_oneHundredSevenDA_1277016753303540240293513]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691294 : Nat.totient 126502556599001999743715691294 = 42167518793754516401651344728 := by
  rw [← show ((([(2, 1), (3, 1), (580984003, 1), (36289741755879292183, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_580984003, prime_oneHundredSevenDA_36289741755879292183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691295 : Nat.totient 126502556599001999743715691295 = 95190441085495094553888537600 := by
  rw [← show ((([(5, 1), (17, 1), (1627, 1), (914729792103850462733401, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_17, prime_oneHundredSevenDA_1627, prime_oneHundredSevenDA_914729792103850462733401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691296 : Nat.totient 126502556599001999743715691296 = 51361940224736767053833448960 := by
  rw [← show ((([(2, 5), (7, 2), (19, 1), (1058087831, 1), (4013080982331173, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_7, prime_oneHundredSevenDA_19, prime_oneHundredSevenDA_1058087831, prime_oneHundredSevenDA_4013080982331173]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691297 : Nat.totient 126502556599001999743715691297 = 82540614451233047075256877056 := by
  rw [← show ((([(3, 2), (47, 1), (1748119, 1), (6087233, 1), (28103992226657, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_47, prime_oneHundredSevenDA_1748119, prime_oneHundredSevenDA_6087233, prime_oneHundredSevenDA_28103992226657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691298 : Nat.totient 126502556599001999743715691298 = 61758648637771077342600062400 := by
  rw [← show ((([(2, 1), (43, 1), (2851, 1), (515945268485973912636593, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_43, prime_oneHundredSevenDA_2851, prime_oneHundredSevenDA_515945268485973912636593]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691299 : Nat.totient 126502556599001999743715691299 = 125998562348992874181028009000 := by
  rw [← show ((([(251, 1), (206331898307, 1), (2442638552418707, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_251, prime_oneHundredSevenDA_206331898307, prime_oneHundredSevenDA_2442638552418707]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691300 : Nat.totient 126502556599001999743715691300 = 33732368165610622906809340160 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (20483, 1), (20586593207212810581737, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_2, prime_oneHundredSevenDA_3, prime_oneHundredSevenDA_5, prime_oneHundredSevenDA_20483, prime_oneHundredSevenDA_20586593207212810581737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredSevenDA_126502556599001999743715691301 : Nat.totient 126502556599001999743715691301 = 126502556599001999743715691300 := by
  rw [← show ((([(126502556599001999743715691301, 1)] : List FactorBlock).map factorBlockValue).prod) = 126502556599001999743715691301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredSevenDA_126502556599001999743715691301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredSevenDA : certifiedKill 1 126502556599001999743715691199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredSevenDA_126502556599001999743715691200, phi_oneHundredSevenDA_126502556599001999743715691201, phi_oneHundredSevenDA_126502556599001999743715691202,
    phi_oneHundredSevenDA_126502556599001999743715691203, phi_oneHundredSevenDA_126502556599001999743715691204, phi_oneHundredSevenDA_126502556599001999743715691205,
    phi_oneHundredSevenDA_126502556599001999743715691206, phi_oneHundredSevenDA_126502556599001999743715691207, phi_oneHundredSevenDA_126502556599001999743715691208,
    phi_oneHundredSevenDA_126502556599001999743715691209, phi_oneHundredSevenDA_126502556599001999743715691210, phi_oneHundredSevenDA_126502556599001999743715691211,
    phi_oneHundredSevenDA_126502556599001999743715691212, phi_oneHundredSevenDA_126502556599001999743715691213, phi_oneHundredSevenDA_126502556599001999743715691214,
    phi_oneHundredSevenDA_126502556599001999743715691215, phi_oneHundredSevenDA_126502556599001999743715691216, phi_oneHundredSevenDA_126502556599001999743715691217,
    phi_oneHundredSevenDA_126502556599001999743715691218, phi_oneHundredSevenDA_126502556599001999743715691219, phi_oneHundredSevenDA_126502556599001999743715691220,
    phi_oneHundredSevenDA_126502556599001999743715691221, phi_oneHundredSevenDA_126502556599001999743715691222, phi_oneHundredSevenDA_126502556599001999743715691223,
    phi_oneHundredSevenDA_126502556599001999743715691224, phi_oneHundredSevenDA_126502556599001999743715691225, phi_oneHundredSevenDA_126502556599001999743715691226,
    phi_oneHundredSevenDA_126502556599001999743715691227, phi_oneHundredSevenDA_126502556599001999743715691228, phi_oneHundredSevenDA_126502556599001999743715691229,
    phi_oneHundredSevenDA_126502556599001999743715691230, phi_oneHundredSevenDA_126502556599001999743715691231, phi_oneHundredSevenDA_126502556599001999743715691232,
    phi_oneHundredSevenDA_126502556599001999743715691233, phi_oneHundredSevenDA_126502556599001999743715691234, phi_oneHundredSevenDA_126502556599001999743715691235,
    phi_oneHundredSevenDA_126502556599001999743715691236, phi_oneHundredSevenDA_126502556599001999743715691237, phi_oneHundredSevenDA_126502556599001999743715691238,
    phi_oneHundredSevenDA_126502556599001999743715691239, phi_oneHundredSevenDA_126502556599001999743715691240, phi_oneHundredSevenDA_126502556599001999743715691241,
    phi_oneHundredSevenDA_126502556599001999743715691242, phi_oneHundredSevenDA_126502556599001999743715691243, phi_oneHundredSevenDA_126502556599001999743715691244,
    phi_oneHundredSevenDA_126502556599001999743715691245, phi_oneHundredSevenDA_126502556599001999743715691246, phi_oneHundredSevenDA_126502556599001999743715691247,
    phi_oneHundredSevenDA_126502556599001999743715691248, phi_oneHundredSevenDA_126502556599001999743715691249, phi_oneHundredSevenDA_126502556599001999743715691250,
    phi_oneHundredSevenDA_126502556599001999743715691251, phi_oneHundredSevenDA_126502556599001999743715691252, phi_oneHundredSevenDA_126502556599001999743715691253,
    phi_oneHundredSevenDA_126502556599001999743715691254, phi_oneHundredSevenDA_126502556599001999743715691255, phi_oneHundredSevenDA_126502556599001999743715691256,
    phi_oneHundredSevenDA_126502556599001999743715691257, phi_oneHundredSevenDA_126502556599001999743715691258, phi_oneHundredSevenDA_126502556599001999743715691259,
    phi_oneHundredSevenDA_126502556599001999743715691260, phi_oneHundredSevenDA_126502556599001999743715691261, phi_oneHundredSevenDA_126502556599001999743715691262,
    phi_oneHundredSevenDA_126502556599001999743715691263, phi_oneHundredSevenDA_126502556599001999743715691264, phi_oneHundredSevenDA_126502556599001999743715691265,
    phi_oneHundredSevenDA_126502556599001999743715691266, phi_oneHundredSevenDA_126502556599001999743715691267, phi_oneHundredSevenDA_126502556599001999743715691268,
    phi_oneHundredSevenDA_126502556599001999743715691269, phi_oneHundredSevenDA_126502556599001999743715691270, phi_oneHundredSevenDA_126502556599001999743715691271,
    phi_oneHundredSevenDA_126502556599001999743715691272, phi_oneHundredSevenDA_126502556599001999743715691273, phi_oneHundredSevenDA_126502556599001999743715691274,
    phi_oneHundredSevenDA_126502556599001999743715691275, phi_oneHundredSevenDA_126502556599001999743715691276, phi_oneHundredSevenDA_126502556599001999743715691277,
    phi_oneHundredSevenDA_126502556599001999743715691278, phi_oneHundredSevenDA_126502556599001999743715691279, phi_oneHundredSevenDA_126502556599001999743715691280,
    phi_oneHundredSevenDA_126502556599001999743715691281, phi_oneHundredSevenDA_126502556599001999743715691282, phi_oneHundredSevenDA_126502556599001999743715691283,
    phi_oneHundredSevenDA_126502556599001999743715691284, phi_oneHundredSevenDA_126502556599001999743715691285, phi_oneHundredSevenDA_126502556599001999743715691286,
    phi_oneHundredSevenDA_126502556599001999743715691287, phi_oneHundredSevenDA_126502556599001999743715691288, phi_oneHundredSevenDA_126502556599001999743715691289,
    phi_oneHundredSevenDA_126502556599001999743715691290, phi_oneHundredSevenDA_126502556599001999743715691291, phi_oneHundredSevenDA_126502556599001999743715691292,
    phi_oneHundredSevenDA_126502556599001999743715691293, phi_oneHundredSevenDA_126502556599001999743715691294, phi_oneHundredSevenDA_126502556599001999743715691295,
    phi_oneHundredSevenDA_126502556599001999743715691296, phi_oneHundredSevenDA_126502556599001999743715691297, phi_oneHundredSevenDA_126502556599001999743715691298,
    phi_oneHundredSevenDA_126502556599001999743715691299, phi_oneHundredSevenDA_126502556599001999743715691300, phi_oneHundredSevenDA_126502556599001999743715691301]

end TotientTailPeriodKiller
end Erdos249257
