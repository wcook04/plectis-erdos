import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredThirtyFiveECFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredThirtyFiveECFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredThirtyFiveECFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredThirtyFiveECFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredThirtyFiveECFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredThirtyFiveECFastPow a n * oneHundredThirtyFiveECFastPow a n * a else oneHundredThirtyFiveECFastPow a n * oneHundredThirtyFiveECFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredThirtyFiveEC_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_547 : Nat.Prime 547 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_683 : Nat.Prime 683 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_761 : Nat.Prime 761 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_773 : Nat.Prime 773 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_823 : Nat.Prime 823 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_997 : Nat.Prime 997 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1063 : Nat.Prime 1063 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1097 : Nat.Prime 1097 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1151 : Nat.Prime 1151 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1201 : Nat.Prime 1201 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1259 : Nat.Prime 1259 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1381 : Nat.Prime 1381 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1409 : Nat.Prime 1409 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1427 : Nat.Prime 1427 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1553 : Nat.Prime 1553 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1699 : Nat.Prime 1699 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1759 : Nat.Prime 1759 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1901 : Nat.Prime 1901 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1979 : Nat.Prime 1979 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1987 : Nat.Prime 1987 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1997 : Nat.Prime 1997 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2011 : Nat.Prime 2011 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2153 : Nat.Prime 2153 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2179 : Nat.Prime 2179 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2203 : Nat.Prime 2203 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2207 : Nat.Prime 2207 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2237 : Nat.Prime 2237 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2417 : Nat.Prime 2417 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2633 : Nat.Prime 2633 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2693 : Nat.Prime 2693 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2851 : Nat.Prime 2851 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2939 : Nat.Prime 2939 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3023 : Nat.Prime 3023 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3079 : Nat.Prime 3079 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3083 : Nat.Prime 3083 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3271 : Nat.Prime 3271 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3313 : Nat.Prime 3313 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3331 : Nat.Prime 3331 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3853 : Nat.Prime 3853 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4133 : Nat.Prime 4133 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4273 : Nat.Prime 4273 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4703 : Nat.Prime 4703 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4729 : Nat.Prime 4729 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4793 : Nat.Prime 4793 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4817 : Nat.Prime 4817 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4933 : Nat.Prime 4933 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5021 : Nat.Prime 5021 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5119 : Nat.Prime 5119 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5449 : Nat.Prime 5449 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5569 : Nat.Prime 5569 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5749 : Nat.Prime 5749 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5897 : Nat.Prime 5897 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6011 : Nat.Prime 6011 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6089 : Nat.Prime 6089 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6113 : Nat.Prime 6113 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6983 : Nat.Prime 6983 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_7213 : Nat.Prime 7213 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_7741 : Nat.Prime 7741 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_7817 : Nat.Prime 7817 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_8527 : Nat.Prime 8527 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_8677 : Nat.Prime 8677 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_8779 : Nat.Prime 8779 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9337 : Nat.Prime 9337 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9341 : Nat.Prime 9341 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9613 : Nat.Prime 9613 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_10733 : Nat.Prime 10733 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11701 : Nat.Prime 11701 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11909 : Nat.Prime 11909 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12329 : Nat.Prime 12329 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12487 : Nat.Prime 12487 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12503 : Nat.Prime 12503 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12689 : Nat.Prime 12689 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12893 : Nat.Prime 12893 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13151 : Nat.Prime 13151 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13267 : Nat.Prime 13267 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13441 : Nat.Prime 13441 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14033 : Nat.Prime 14033 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14249 : Nat.Prime 14249 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14387 : Nat.Prime 14387 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14717 : Nat.Prime 14717 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14779 : Nat.Prime 14779 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14947 : Nat.Prime 14947 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_15391 : Nat.Prime 15391 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_16007 : Nat.Prime 16007 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_16453 : Nat.Prime 16453 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_17077 : Nat.Prime 17077 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_17597 : Nat.Prime 17597 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_17827 : Nat.Prime 17827 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_19141 : Nat.Prime 19141 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_19483 : Nat.Prime 19483 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_23297 : Nat.Prime 23297 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_24337 : Nat.Prime 24337 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_24821 : Nat.Prime 24821 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25189 : Nat.Prime 25189 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25463 : Nat.Prime 25463 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25841 : Nat.Prime 25841 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_26119 : Nat.Prime 26119 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_26459 : Nat.Prime 26459 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_26497 : Nat.Prime 26497 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_26573 : Nat.Prime 26573 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_28403 : Nat.Prime 28403 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_28603 : Nat.Prime 28603 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_29437 : Nat.Prime 29437 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_30029 : Nat.Prime 30029 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_32911 : Nat.Prime 32911 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_33721 : Nat.Prime 33721 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_34457 : Nat.Prime 34457 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_37277 : Nat.Prime 37277 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_40009 : Nat.Prime 40009 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_40487 : Nat.Prime 40487 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_40559 : Nat.Prime 40559 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_41257 : Nat.Prime 41257 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_42379 : Nat.Prime 42379 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_42667 : Nat.Prime 42667 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_45959 : Nat.Prime 45959 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_48119 : Nat.Prime 48119 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_48539 : Nat.Prime 48539 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_48571 : Nat.Prime 48571 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_55921 : Nat.Prime 55921 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_58049 : Nat.Prime 58049 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_61153 : Nat.Prime 61153 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_65809 : Nat.Prime 65809 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_67231 : Nat.Prime 67231 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_72073 : Nat.Prime 72073 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_73327 : Nat.Prime 73327 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_75619 : Nat.Prime 75619 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_79847 : Nat.Prime 79847 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_80111 : Nat.Prime 80111 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_80513 : Nat.Prime 80513 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_80629 : Nat.Prime 80629 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_85193 : Nat.Prime 85193 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_89833 : Nat.Prime 89833 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_99181 : Nat.Prime 99181 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_106321 : Nat.Prime 106321 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_107071 : Nat.Prime 107071 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_108709 : Nat.Prime 108709 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_113363 : Nat.Prime 113363 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_120383 : Nat.Prime 120383 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_120917 : Nat.Prime 120917 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_122701 : Nat.Prime 122701 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_123731 : Nat.Prime 123731 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_129803 : Nat.Prime 129803 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_144341 : Nat.Prime 144341 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_146173 : Nat.Prime 146173 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_147047 : Nat.Prime 147047 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_152597 : Nat.Prime 152597 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_152753 : Nat.Prime 152753 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_154213 : Nat.Prime 154213 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_160907 : Nat.Prime 160907 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_168263 : Nat.Prime 168263 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_177269 : Nat.Prime 177269 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_178489 : Nat.Prime 178489 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_183059 : Nat.Prime 183059 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_188911 : Nat.Prime 188911 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_211231 : Nat.Prime 211231 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_212557 : Nat.Prime 212557 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_216373 : Nat.Prime 216373 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_222791 : Nat.Prime 222791 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_228233 : Nat.Prime 228233 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_228331 : Nat.Prime 228331 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_242057 : Nat.Prime 242057 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_246151 : Nat.Prime 246151 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_248621 : Nat.Prime 248621 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_260011 : Nat.Prime 260011 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_265007 : Nat.Prime 265007 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_284833 : Nat.Prime 284833 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_288689 : Nat.Prime 288689 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_300331 : Nat.Prime 300331 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_334093 : Nat.Prime 334093 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_343433 : Nat.Prime 343433 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_388363 : Nat.Prime 388363 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_388373 : Nat.Prime 388373 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_394577 : Nat.Prime 394577 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_412127 : Nat.Prime 412127 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_412561 : Nat.Prime 412561 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_438937 : Nat.Prime 438937 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_439799 : Nat.Prime 439799 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_444131 : Nat.Prime 444131 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_453029 : Nat.Prime 453029 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_533999 : Nat.Prime 533999 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_537181 : Nat.Prime 537181 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_552137 : Nat.Prime 552137 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_631751 : Nat.Prime 631751 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_643961 : Nat.Prime 643961 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_687923 : Nat.Prime 687923 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_701609 : Nat.Prime 701609 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_733813 : Nat.Prime 733813 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_797869 : Nat.Prime 797869 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_805843 : Nat.Prime 805843 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_862409 : Nat.Prime 862409 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_880861 : Nat.Prime 880861 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_882253 : Nat.Prime 882253 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_900929 : Nat.Prime 900929 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_937241 : Nat.Prime 937241 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_964433 : Nat.Prime 964433 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1011443 : Nat.Prime 1011443 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1016947 : Nat.Prime 1016947 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1099249 : Nat.Prime 1099249 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1128151 : Nat.Prime 1128151 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1129153 : Nat.Prime 1129153 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1152937 : Nat.Prime 1152937 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1220249 : Nat.Prime 1220249 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1243169 : Nat.Prime 1243169 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1379513 : Nat.Prime 1379513 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1408709 : Nat.Prime 1408709 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1426127 : Nat.Prime 1426127 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1438033 : Nat.Prime 1438033 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1458631 : Nat.Prime 1458631 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1521133 : Nat.Prime 1521133 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1602869 : Nat.Prime 1602869 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1603067 : Nat.Prime 1603067 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1772971 : Nat.Prime 1772971 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1990787 : Nat.Prime 1990787 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_1996723 : Nat.Prime 1996723 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2135687 : Nat.Prime 2135687 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2290829 : Nat.Prime 2290829 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2397581 : Nat.Prime 2397581 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2518619 : Nat.Prime 2518619 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2578351 : Nat.Prime 2578351 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_2977523 : Nat.Prime 2977523 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3118523 : Nat.Prime 3118523 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3122179 : Nat.Prime 3122179 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3670123 : Nat.Prime 3670123 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_3831643 : Nat.Prime 3831643 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4476319 : Nat.Prime 4476319 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4507537 : Nat.Prime 4507537 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4671071 : Nat.Prime 4671071 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4672097 : Nat.Prime 4672097 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4676669 : Nat.Prime 4676669 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4811171 : Nat.Prime 4811171 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_4966519 : Nat.Prime 4966519 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5037091 : Nat.Prime 5037091 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5143253 : Nat.Prime 5143253 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5816549 : Nat.Prime 5816549 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_5913109 : Nat.Prime 5913109 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_6280289 : Nat.Prime 6280289 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_8095547 : Nat.Prime 8095547 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_8992483 : Nat.Prime 8992483 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9266407 : Nat.Prime 9266407 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9296759 : Nat.Prime 9296759 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_9390221 : Nat.Prime 9390221 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_10210243 : Nat.Prime 10210243 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_10420363 : Nat.Prime 10420363 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11014981 : Nat.Prime 11014981 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11511733 : Nat.Prime 11511733 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_11593723 : Nat.Prime 11593723 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_12139741 : Nat.Prime 12139741 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13144577 : Nat.Prime 13144577 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13426529 : Nat.Prime 13426529 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_13680577 : Nat.Prime 13680577 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_14885711 : Nat.Prime 14885711 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_15571489 : Nat.Prime 15571489 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_16797857 : Nat.Prime 16797857 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_23314271 : Nat.Prime 23314271 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25069433 : Nat.Prime 25069433 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25289651 : Nat.Prime 25289651 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_25375709 : Nat.Prime 25375709 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_26133853 : Nat.Prime 26133853 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_28421557 : Nat.Prime 28421557 := by norm_num

private theorem prime_oneHundredThirtyFiveEC_30740813 : Nat.Prime 30740813 := by
  apply lucas_primality 30740813 (2 : ZMod 30740813)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (265007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (265007, 1)] : List FactorBlock).map factorBlockValue).prod) = 30740813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_265007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 30740813) ^ 15370406 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 30740813) ^ 1060028 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 30740813) ^ 116 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_31458437 : Nat.Prime 31458437 := by
  apply lucas_primality 31458437 (2 : ZMod 31458437)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (212557, 1)] : List FactorBlock).map factorBlockValue).prod) = 31458437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_212557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31458437) ^ 15729218 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 850228 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31458437) ^ 148 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_31967051 : Nat.Prime 31967051 := by
  apply lucas_primality 31967051 (2 : ZMod 31967051)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (47, 1), (61, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (47, 1), (61, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 31967051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31967051) ^ 15983525 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31967051) ^ 6393410 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31967051) ^ 680150 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31967051) ^ 524050 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 31967051) ^ 143350 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_32246411 : Nat.Prime 32246411 := by
  apply lucas_primality 32246411 (2 : ZMod 32246411)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (65809, 1)] : List FactorBlock).map factorBlockValue).prod) = 32246411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_65809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32246411) ^ 16123205 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 6449282 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 4606630 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 32246411) ^ 490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_33346693 : Nat.Prime 33346693 := by
  apply lucas_primality 33346693 (2 : ZMod 33346693)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (73, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (73, 1), (12689, 1)] : List FactorBlock).map factorBlockValue).prod) = 33346693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_12689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 33346693) ^ 16673346 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 33346693) ^ 11115564 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 33346693) ^ 456804 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 33346693) ^ 2628 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_33677233 : Nat.Prime 33677233 := by
  apply lucas_primality 33677233 (5 : ZMod 33677233)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (701609, 1)] : List FactorBlock).map factorBlockValue).prod) = 33677233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_701609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 33677233) ^ 16838616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 11225744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 33677233) ^ 48 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_35201629 : Nat.Prime 35201629 := by
  apply lucas_primality 35201629 (6 : ZMod 35201629)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (11, 1), (17, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (11, 1), (17, 1), (83, 1)] : List FactorBlock).map factorBlockValue).prod) = 35201629 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_83
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 35201629) ^ 17600814 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 35201629) ^ 11733876 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 35201629) ^ 5028804 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 35201629) ^ 3200148 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 35201629) ^ 2070684 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 35201629) ^ 424116 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_36507193 : Nat.Prime 36507193 := by
  apply lucas_primality 36507193 (5 : ZMod 36507193)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1521133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1521133, 1)] : List FactorBlock).map factorBlockValue).prod) = 36507193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_1521133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 36507193) ^ 18253596 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36507193) ^ 12169064 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36507193) ^ 24 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_41768329 : Nat.Prime 41768329 := by
  apply lucas_primality 41768329 (13 : ZMod 41768329)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (248621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (248621, 1)] : List FactorBlock).map factorBlockValue).prod) = 41768329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_248621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 41768329) ^ 20884164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 41768329) ^ 13922776 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 41768329) ^ 5966904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 41768329) ^ 168 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_45399371 : Nat.Prime 45399371 := by
  apply lucas_primality 45399371 (2 : ZMod 45399371)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (37, 1), (122701, 1)] : List FactorBlock).map factorBlockValue).prod) = 45399371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_122701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 45399371) ^ 22699685 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 9079874 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 1227010 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 45399371) ^ 370 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_46256069 : Nat.Prime 46256069 := by
  apply lucas_primality 46256069 (2 : ZMod 46256069)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (53, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (53, 1), (5897, 1)] : List FactorBlock).map factorBlockValue).prod) = 46256069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_5897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46256069) ^ 23128034 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 46256069) ^ 1250164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 46256069) ^ 872756 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 46256069) ^ 7844 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_51941039 : Nat.Prime 51941039 := by
  apply lucas_primality 51941039 (19 : ZMod 51941039)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1129153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1129153, 1)] : List FactorBlock).map factorBlockValue).prod) = 51941039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_1129153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (19 : ZMod 51941039) ^ 25970519 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (19 : ZMod 51941039) ^ 2258306 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (19 : ZMod 51941039) ^ 46 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_52474501 : Nat.Prime 52474501 := by
  apply lucas_primality 52474501 (14 : ZMod 52474501)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 3), (13, 2), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 52474501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 52474501) ^ 26237250 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 17491500 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 10494900 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 4036500 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 52474501) ^ 2281500 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_55460903 : Nat.Prime 55460903 := by
  apply lucas_primality 55460903 (5 : ZMod 55460903)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (17, 1), (199, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (17, 1), (199, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 55460903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_199
      · exact prime_oneHundredThirtyFiveEC_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 55460903) ^ 27730451 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 55460903) ^ 7922986 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 55460903) ^ 3262406 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 55460903) ^ 278698 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 55460903) ^ 47362 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_55518473 : Nat.Prime 55518473 := by
  apply lucas_primality 55518473 (3 : ZMod 55518473)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (151, 1), (45959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (151, 1), (45959, 1)] : List FactorBlock).map factorBlockValue).prod) = 55518473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_151
      · exact prime_oneHundredThirtyFiveEC_45959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 55518473) ^ 27759236 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 55518473) ^ 367672 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 55518473) ^ 1208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_59550461 : Nat.Prime 59550461 := by
  apply lucas_primality 59550461 (2 : ZMod 59550461)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2977523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2977523, 1)] : List FactorBlock).map factorBlockValue).prod) = 59550461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_2977523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59550461) ^ 29775230 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59550461) ^ 11910092 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59550461) ^ 20 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_59598493 : Nat.Prime 59598493 := by
  apply lucas_primality 59598493 (2 : ZMod 59598493)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (151, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (151, 1), (1061, 1)] : List FactorBlock).map factorBlockValue).prod) = 59598493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_151
      · exact prime_oneHundredThirtyFiveEC_1061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59598493) ^ 29799246 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59598493) ^ 19866164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59598493) ^ 1922532 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59598493) ^ 394692 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 59598493) ^ 56172 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_59723611 : Nat.Prime 59723611 := by
  apply lucas_primality 59723611 (14 : ZMod 59723611)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (1990787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (1990787, 1)] : List FactorBlock).map factorBlockValue).prod) = 59723611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_1990787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 59723611) ^ 29861805 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 59723611) ^ 19907870 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 59723611) ^ 11944722 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 59723611) ^ 30 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_149
      · exact prime_oneHundredThirtyFiveEC_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_68662933 : Nat.Prime 68662933 := by
  apply lucas_primality 68662933 (2 : ZMod 68662933)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 2), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 2), (1523, 1)] : List FactorBlock).map factorBlockValue).prod) = 68662933 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_1523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68662933) ^ 34331466 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68662933) ^ 22887644 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68662933) ^ 5281764 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68662933) ^ 4038996 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68662933) ^ 45084 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_75121769 : Nat.Prime 75121769 := by
  apply lucas_primality 75121769 (3 : ZMod 75121769)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (9390221, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (9390221, 1)] : List FactorBlock).map factorBlockValue).prod) = 75121769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_9390221
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 75121769) ^ 37560884 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 75121769) ^ 8 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_75363469 : Nat.Prime 75363469 := by
  apply lucas_primality 75363469 (7 : ZMod 75363469)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (6280289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (6280289, 1)] : List FactorBlock).map factorBlockValue).prod) = 75363469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_6280289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 75363469) ^ 37681734 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 75363469) ^ 25121156 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 75363469) ^ 12 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_79494491 : Nat.Prime 79494491 := by
  apply lucas_primality 79494491 (6 : ZMod 79494491)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (41, 2), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (41, 2), (4729, 1)] : List FactorBlock).map factorBlockValue).prod) = 79494491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_4729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 79494491) ^ 39747245 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79494491) ^ 15898898 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79494491) ^ 1938890 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79494491) ^ 16810 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_81647611 : Nat.Prime 81647611 := by
  apply lucas_primality 81647611 (12 : ZMod 81647611)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 1), (401, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 1), (401, 1), (617, 1)] : List FactorBlock).map factorBlockValue).prod) = 81647611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_401
      · exact prime_oneHundredThirtyFiveEC_617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 81647611) ^ 40823805 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 81647611) ^ 27215870 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 81647611) ^ 16329522 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 81647611) ^ 7422510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 81647611) ^ 203610 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 81647611) ^ 132330 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_83780407 : Nat.Prime 83780407 := by
  apply lucas_primality 83780407 (3 : ZMod 83780407)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (103, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (103, 1), (5021, 1)] : List FactorBlock).map factorBlockValue).prod) = 83780407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_103
      · exact prime_oneHundredThirtyFiveEC_5021
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 83780407) ^ 41890203 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 83780407) ^ 27926802 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 83780407) ^ 813402 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 83780407) ^ 16686 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_92512139 : Nat.Prime 92512139 := by
  apply lucas_primality 92512139 (2 : ZMod 92512139)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (46256069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (46256069, 1)] : List FactorBlock).map factorBlockValue).prod) = 92512139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_46256069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 92512139) ^ 46256069 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 92512139) ^ 2 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_110796689 : Nat.Prime 110796689 := by
  apply lucas_primality 110796689 (3 : ZMod 110796689)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) = 110796689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_103
      · exact prime_oneHundredThirtyFiveEC_67231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110796689) ^ 55398344 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1075696 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1648 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_110921807 : Nat.Prime 110921807 := by
  apply lucas_primality 110921807 (5 : ZMod 110921807)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55460903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55460903, 1)] : List FactorBlock).map factorBlockValue).prod) = 110921807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_55460903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 110921807) ^ 55460903 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 110921807) ^ 2 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_115937231 : Nat.Prime 115937231 := by
  apply lucas_primality 115937231 (7 : ZMod 115937231)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11593723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11593723, 1)] : List FactorBlock).map factorBlockValue).prod) = 115937231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_11593723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 115937231) ^ 57968615 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 115937231) ^ 23187446 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 115937231) ^ 10 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_129007363 : Nat.Prime 129007363 := by
  apply lucas_primality 129007363 (11 : ZMod 129007363)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (127, 1), (15391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (127, 1), (15391, 1)] : List FactorBlock).map factorBlockValue).prod) = 129007363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_127
      · exact prime_oneHundredThirtyFiveEC_15391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 129007363) ^ 64503681 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 129007363) ^ 43002454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 129007363) ^ 11727942 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 129007363) ^ 1015806 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 129007363) ^ 8382 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_223
      · exact prime_oneHundredThirtyFiveEC_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_131518657 : Nat.Prime 131518657 := by
  apply lucas_primality 131518657 (5 : ZMod 131518657)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (228331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (228331, 1)] : List FactorBlock).map factorBlockValue).prod) = 131518657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_228331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 131518657) ^ 65759328 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 131518657) ^ 43839552 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 131518657) ^ 576 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_166741177 : Nat.Prime 166741177 := by
  apply lucas_primality 166741177 (10 : ZMod 166741177)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (163, 1), (6089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (163, 1), (6089, 1)] : List FactorBlock).map factorBlockValue).prod) = 166741177 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_163
      · exact prime_oneHundredThirtyFiveEC_6089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 166741177) ^ 83370588 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 166741177) ^ 55580392 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 166741177) ^ 23820168 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 166741177) ^ 1022952 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 166741177) ^ 27384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_172669379 : Nat.Prime 172669379 := by
  apply lucas_primality 172669379 (2 : ZMod 172669379)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (761, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (761, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 172669379 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_761
      · exact prime_oneHundredThirtyFiveEC_853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 172669379) ^ 86334689 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 172669379) ^ 24667054 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 172669379) ^ 9087862 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 172669379) ^ 226898 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 172669379) ^ 202426 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_184444879 : Nat.Prime 184444879 := by
  apply lucas_primality 184444879 (3 : ZMod 184444879)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30740813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30740813, 1)] : List FactorBlock).map factorBlockValue).prod) = 184444879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_30740813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 184444879) ^ 92222439 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 184444879) ^ 61481626 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 184444879) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_184602589 : Nat.Prime 184602589 := by
  apply lucas_primality 184602589 (7 : ZMod 184602589)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2203, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2203, 1), (6983, 1)] : List FactorBlock).map factorBlockValue).prod) = 184602589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2203
      · exact prime_oneHundredThirtyFiveEC_6983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 184602589) ^ 92301294 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 184602589) ^ 61534196 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 184602589) ^ 83796 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 184602589) ^ 26436 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_202063399 : Nat.Prime 202063399 := by
  apply lucas_primality 202063399 (3 : ZMod 202063399)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (33677233, 1)] : List FactorBlock).map factorBlockValue).prod) = 202063399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_33677233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 202063399) ^ 101031699 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 67354466 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 202063399) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_204209849 : Nat.Prime 204209849 := by
  apply lucas_primality 204209849 (3 : ZMod 204209849)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (41, 1), (53, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (41, 1), (53, 1), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 204209849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 204209849) ^ 102104924 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 204209849) ^ 12012344 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 204209849) ^ 4980728 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 204209849) ^ 3853016 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 204209849) ^ 295528 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_212348441 : Nat.Prime 212348441 := by
  apply lucas_primality 212348441 (3 : ZMod 212348441)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (29, 1), (183059, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (29, 1), (183059, 1)] : List FactorBlock).map factorBlockValue).prod) = 212348441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_183059
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 212348441) ^ 106174220 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 212348441) ^ 42469688 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 212348441) ^ 7322360 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 212348441) ^ 1160 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_248048113 : Nat.Prime 248048113 := by
  apply lucas_primality 248048113 (7 : ZMod 248048113)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 248048113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 248048113) ^ 124024056 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 82682704 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19080624 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 8001552 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19344 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_250145449 : Nat.Prime 250145449 := by
  apply lucas_primality 250145449 (17 : ZMod 250145449)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (31, 1), (43, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (31, 1), (43, 1), (1117, 1)] : List FactorBlock).map factorBlockValue).prod) = 250145449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_43
      · exact prime_oneHundredThirtyFiveEC_1117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 250145449) ^ 125072724 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 250145449) ^ 83381816 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 250145449) ^ 35735064 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 250145449) ^ 8069208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 250145449) ^ 5817336 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 250145449) ^ 223944 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_251798293 : Nat.Prime 251798293 := by
  apply lucas_primality 251798293 (6 : ZMod 251798293)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (359, 1), (19483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (359, 1), (19483, 1)] : List FactorBlock).map factorBlockValue).prod) = 251798293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_359
      · exact prime_oneHundredThirtyFiveEC_19483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 251798293) ^ 125899146 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 251798293) ^ 83932764 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 251798293) ^ 701388 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 251798293) ^ 12924 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_261637433 : Nat.Prime 261637433 := by
  apply lucas_primality 261637433 (3 : ZMod 261637433)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (4672097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (4672097, 1)] : List FactorBlock).map factorBlockValue).prod) = 261637433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_4672097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 261637433) ^ 130818716 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 261637433) ^ 37376776 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 261637433) ^ 56 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_287010313 : Nat.Prime 287010313 := by
  apply lucas_primality 287010313 (10 : ZMod 287010313)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (67, 1), (178489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (67, 1), (178489, 1)] : List FactorBlock).map factorBlockValue).prod) = 287010313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_67
      · exact prime_oneHundredThirtyFiveEC_178489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 287010313) ^ 143505156 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 287010313) ^ 95670104 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 287010313) ^ 4283736 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 287010313) ^ 1608 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_295305187 : Nat.Prime 295305187 := by
  apply lucas_primality 295305187 (2 : ZMod 295305187)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (149, 1), (30029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (149, 1), (30029, 1)] : List FactorBlock).map factorBlockValue).prod) = 295305187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_149
      · exact prime_oneHundredThirtyFiveEC_30029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 295305187) ^ 147652593 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 295305187) ^ 98435062 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 295305187) ^ 26845926 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 295305187) ^ 1981914 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 295305187) ^ 9834 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_311517887 : Nat.Prime 311517887 := by
  apply lucas_primality 311517887 (5 : ZMod 311517887)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (1823, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (1823, 1), (1987, 1)] : List FactorBlock).map factorBlockValue).prod) = 311517887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_43
      · exact prime_oneHundredThirtyFiveEC_1823
      · exact prime_oneHundredThirtyFiveEC_1987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 311517887) ^ 155758943 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 311517887) ^ 7244602 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 311517887) ^ 170882 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 311517887) ^ 156778 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_314847007 : Nat.Prime 314847007 := by
  apply lucas_primality 314847007 (5 : ZMod 314847007)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (52474501, 1)] : List FactorBlock).map factorBlockValue).prod) = 314847007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_52474501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 314847007) ^ 157423503 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 104949002 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 314847007) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_357725681 : Nat.Prime 357725681 := by
  apply lucas_primality 357725681 (3 : ZMod 357725681)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (13, 2), (26459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (13, 2), (26459, 1)] : List FactorBlock).map factorBlockValue).prod) = 357725681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_26459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 357725681) ^ 178862840 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 357725681) ^ 71545136 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 357725681) ^ 27517360 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 357725681) ^ 13520 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_359823089 : Nat.Prime 359823089 := by
  apply lucas_primality 359823089 (3 : ZMod 359823089)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (1087, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (1087, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 359823089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_1087
      · exact prime_oneHundredThirtyFiveEC_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 359823089) ^ 179911544 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 359823089) ^ 21166064 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 359823089) ^ 331024 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 359823089) ^ 295664 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_12539
      · exact prime_oneHundredThirtyFiveEC_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_394337311 : Nat.Prime 394337311 := by
  apply lucas_primality 394337311 (11 : ZMod 394337311)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13144577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13144577, 1)] : List FactorBlock).map factorBlockValue).prod) = 394337311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13144577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 394337311) ^ 197168655 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 394337311) ^ 131445770 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 394337311) ^ 78867462 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 394337311) ^ 30 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_402546029 : Nat.Prime 402546029 := by
  apply lucas_primality 402546029 (2 : ZMod 402546029)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3853, 1), (26119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3853, 1), (26119, 1)] : List FactorBlock).map factorBlockValue).prod) = 402546029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3853
      · exact prime_oneHundredThirtyFiveEC_26119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 402546029) ^ 201273014 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 402546029) ^ 104476 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 402546029) ^ 15412 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_523274867 : Nat.Prime 523274867 := by
  apply lucas_primality 523274867 (2 : ZMod 523274867)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (261637433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (261637433, 1)] : List FactorBlock).map factorBlockValue).prod) = 523274867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_261637433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 523274867) ^ 261637433 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 523274867) ^ 2 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_540182551 : Nat.Prime 540182551 := by
  apply lucas_primality 540182551 (17 : ZMod 540182551)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (1049, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) = 540182551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_1049
      · exact prime_oneHundredThirtyFiveEC_3433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 540182551) ^ 270091275 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 180060850 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 108036510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 514950 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 540182551) ^ 157350 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_555817231 : Nat.Prime 555817231 := by
  apply lucas_primality 555817231 (7 : ZMod 555817231)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (479, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (479, 1), (12893, 1)] : List FactorBlock).map factorBlockValue).prod) = 555817231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_479
      · exact prime_oneHundredThirtyFiveEC_12893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 555817231) ^ 277908615 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 555817231) ^ 185272410 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 555817231) ^ 111163446 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 555817231) ^ 1160370 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 555817231) ^ 43110 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_569667919 : Nat.Prime 569667919 := by
  apply lucas_primality 569667919 (3 : ZMod 569667919)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (47, 1), (106321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (47, 1), (106321, 1)] : List FactorBlock).map factorBlockValue).prod) = 569667919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_106321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 569667919) ^ 284833959 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 569667919) ^ 189889306 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 569667919) ^ 29982522 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 569667919) ^ 12120594 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 569667919) ^ 5358 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_600585511 : Nat.Prime 600585511 := by
  apply lucas_primality 600585511 (6 : ZMod 600585511)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (83, 1), (34457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (83, 1), (34457, 1)] : List FactorBlock).map factorBlockValue).prod) = 600585511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_83
      · exact prime_oneHundredThirtyFiveEC_34457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 600585511) ^ 300292755 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 600585511) ^ 200195170 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 600585511) ^ 120117102 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 600585511) ^ 85797930 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 600585511) ^ 7235970 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 600585511) ^ 17430 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_614504323 : Nat.Prime 614504323 := by
  apply lucas_primality 614504323 (2 : ZMod 614504323)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (4733, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 614504323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_4733
      · exact prime_oneHundredThirtyFiveEC_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 614504323) ^ 307252161 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 204834774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 129834 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 614504323) ^ 85194 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_17203
      · exact prime_oneHundredThirtyFiveEC_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_717281353 : Nat.Prime 717281353 := by
  apply lucas_primality 717281353 (5 : ZMod 717281353)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (83, 1), (40009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (83, 1), (40009, 1)] : List FactorBlock).map factorBlockValue).prod) = 717281353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_83
      · exact prime_oneHundredThirtyFiveEC_40009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 717281353) ^ 358640676 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 717281353) ^ 239093784 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 717281353) ^ 8641944 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 717281353) ^ 17928 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_736726649 : Nat.Prime 736726649 := by
  apply lucas_primality 736726649 (11 : ZMod 736726649)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1409, 1), (9337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1409, 1), (9337, 1)] : List FactorBlock).map factorBlockValue).prod) = 736726649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_1409
      · exact prime_oneHundredThirtyFiveEC_9337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 736726649) ^ 368363324 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 736726649) ^ 105246664 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 736726649) ^ 522872 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 736726649) ^ 78904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_131
      · exact prime_oneHundredThirtyFiveEC_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1014344069 : Nat.Prime 1014344069 := by
  apply lucas_primality 1014344069 (2 : ZMod 1014344069)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (433, 1), (25463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (433, 1), (25463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1014344069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_433
      · exact prime_oneHundredThirtyFiveEC_25463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1014344069) ^ 507172034 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014344069) ^ 44101916 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014344069) ^ 2342596 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1014344069) ^ 39836 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1143177577 : Nat.Prime 1143177577 := by
  apply lucas_primality 1143177577 (5 : ZMod 1143177577)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143177577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_25189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1143177577) ^ 571588788 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 381059192 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 36876696 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 18740616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 45384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1220243699 : Nat.Prime 1220243699 := by
  apply lucas_primality 1220243699 (2 : ZMod 1220243699)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (53, 1), (11511733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (53, 1), (11511733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1220243699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_11511733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1220243699) ^ 610121849 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220243699) ^ 23023466 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1220243699) ^ 106 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1392230797 : Nat.Prime 1392230797 := by
  apply lucas_primality 1392230797 (5 : ZMod 1392230797)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (131, 1), (80513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (131, 1), (80513, 1)] : List FactorBlock).map factorBlockValue).prod) = 1392230797 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_131
      · exact prime_oneHundredThirtyFiveEC_80513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1392230797) ^ 696115398 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1392230797) ^ 464076932 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1392230797) ^ 126566436 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1392230797) ^ 10627716 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1392230797) ^ 17292 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1405726849 : Nat.Prime 1405726849 := by
  apply lucas_primality 1405726849 (11 : ZMod 1405726849)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (1220249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (1220249, 1)] : List FactorBlock).map factorBlockValue).prod) = 1405726849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_1220249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 1405726849) ^ 702863424 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405726849) ^ 468575616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1405726849) ^ 1152 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1502435381 : Nat.Prime 1502435381 := by
  apply lucas_primality 1502435381 (2 : ZMod 1502435381)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (75121769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (75121769, 1)] : List FactorBlock).map factorBlockValue).prod) = 1502435381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_75121769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1502435381) ^ 751217690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502435381) ^ 300487076 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1502435381) ^ 20 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1591288781 : Nat.Prime 1591288781 := by
  apply lucas_primality 1591288781 (2 : ZMod 1591288781)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (3079, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (3079, 1), (25841, 1)] : List FactorBlock).map factorBlockValue).prod) = 1591288781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_3079
      · exact prime_oneHundredThirtyFiveEC_25841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1591288781) ^ 795644390 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1591288781) ^ 318257756 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1591288781) ^ 516820 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1591288781) ^ 61580 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1618594963 : Nat.Prime 1618594963 := by
  apply lucas_primality 1618594963 (2 : ZMod 1618594963)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (97, 1), (120917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (97, 1), (120917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1618594963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_97
      · exact prime_oneHundredThirtyFiveEC_120917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1618594963) ^ 809297481 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618594963) ^ 539531654 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618594963) ^ 70373694 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618594963) ^ 16686546 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1618594963) ^ 13386 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1679227807 : Nat.Prime 1679227807 := by
  apply lucas_primality 1679227807 (3 : ZMod 1679227807)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (521, 1), (537181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (521, 1), (537181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1679227807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_521
      · exact prime_oneHundredThirtyFiveEC_537181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1679227807) ^ 839613903 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1679227807) ^ 559742602 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1679227807) ^ 3223086 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1679227807) ^ 3126 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1691041447 : Nat.Prime 1691041447 := by
  apply lucas_primality 1691041447 (3 : ZMod 1691041447)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (29, 1), (1429, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (29, 1), (1429, 1), (2267, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691041447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_1429
      · exact prime_oneHundredThirtyFiveEC_2267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1691041447) ^ 845520723 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691041447) ^ 563680482 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691041447) ^ 58311774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691041447) ^ 1183374 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1691041447) ^ 745938 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1799154887 : Nat.Prime 1799154887 := by
  apply lucas_primality 1799154887 (5 : ZMod 1799154887)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (13426529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (13426529, 1)] : List FactorBlock).map factorBlockValue).prod) = 1799154887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_67
      · exact prime_oneHundredThirtyFiveEC_13426529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1799154887) ^ 899577443 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1799154887) ^ 26853058 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1799154887) ^ 134 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1807803859 : Nat.Prime 1807803859 := by
  apply lucas_primality 1807803859 (2 : ZMod 1807803859)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (587, 1), (73327, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (587, 1), (73327, 1)] : List FactorBlock).map factorBlockValue).prod) = 1807803859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_587
      · exact prime_oneHundredThirtyFiveEC_73327
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1807803859) ^ 903901929 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1807803859) ^ 602601286 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1807803859) ^ 258257694 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1807803859) ^ 3079734 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1807803859) ^ 24654 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1861975811 : Nat.Prime 1861975811 := by
  apply lucas_primality 1861975811 (2 : ZMod 1861975811)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1861975811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_8095547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1861975811) ^ 930987905 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 372395162 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 80955470 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 230 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1889082043 : Nat.Prime 1889082043 := by
  apply lucas_primality 1889082043 (2 : ZMod 1889082043)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (314847007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1889082043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_314847007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1889082043) ^ 944541021 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 629694014 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1889082043) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2115948589 : Nat.Prime 2115948589 := by
  apply lucas_primality 2115948589 (2 : ZMod 2115948589)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (17, 1), (797869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (17, 1), (797869, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115948589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_797869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2115948589) ^ 1057974294 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 705316196 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 162765276 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 124467564 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2115948589) ^ 2652 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2540316523 : Nat.Prime 2540316523 := by
  apply lucas_primality 2540316523 (2 : ZMod 2540316523)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (439, 1), (964433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (439, 1), (964433, 1)] : List FactorBlock).map factorBlockValue).prod) = 2540316523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_439
      · exact prime_oneHundredThirtyFiveEC_964433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2540316523) ^ 1270158261 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540316523) ^ 846772174 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540316523) ^ 5786598 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2540316523) ^ 2634 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3910831549 : Nat.Prime 3910831549 := by
  apply lucas_primality 3910831549 (2 : ZMod 3910831549)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (25069433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (25069433, 1)] : List FactorBlock).map factorBlockValue).prod) = 3910831549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_25069433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3910831549) ^ 1955415774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 1303610516 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 300833196 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3910831549) ^ 156 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4084196981 : Nat.Prime 4084196981 := by
  apply lucas_primality 4084196981 (3 : ZMod 4084196981)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (204209849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (204209849, 1)] : List FactorBlock).map factorBlockValue).prod) = 4084196981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_204209849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4084196981) ^ 2042098490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084196981) ^ 816839396 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4084196981) ^ 20 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6414260233 : Nat.Prime 6414260233 := by
  apply lucas_primality 6414260233 (5 : ZMod 6414260233)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (1171, 1), (228233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (1171, 1), (228233, 1)] : List FactorBlock).map factorBlockValue).prod) = 6414260233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_1171
      · exact prime_oneHundredThirtyFiveEC_228233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6414260233) ^ 3207130116 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6414260233) ^ 2138086744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6414260233) ^ 5477592 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6414260233) ^ 28104 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7556328173 : Nat.Prime 7556328173 := by
  apply lucas_primality 7556328173 (2 : ZMod 7556328173)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1889082043, 1)] : List FactorBlock).map factorBlockValue).prod) = 7556328173 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_1889082043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7556328173) ^ 3778164086 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7556328173) ^ 4 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_9663329381 : Nat.Prime 9663329381 := by
  apply lucas_primality 9663329381 (3 : ZMod 9663329381)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (17, 1), (28421557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (17, 1), (28421557, 1)] : List FactorBlock).map factorBlockValue).prod) = 9663329381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_28421557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 9663329381) ^ 4831664690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 9663329381) ^ 1932665876 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 9663329381) ^ 568431140 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 9663329381) ^ 340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_10146248683 : Nat.Prime 10146248683 := by
  apply lucas_primality 10146248683 (2 : ZMod 10146248683)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1691041447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1691041447, 1)] : List FactorBlock).map factorBlockValue).prod) = 10146248683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_1691041447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10146248683) ^ 5073124341 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10146248683) ^ 3382082894 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10146248683) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_10794929323 : Nat.Prime 10794929323 := by
  apply lucas_primality 10794929323 (2 : ZMod 10794929323)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1799154887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1799154887, 1)] : List FactorBlock).map factorBlockValue).prod) = 10794929323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_1799154887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 10794929323) ^ 5397464661 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10794929323) ^ 3598309774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10794929323) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_10876676611 : Nat.Prime 10876676611 := by
  apply lucas_primality 10876676611 (2 : ZMod 10876676611)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (73, 1), (4966519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (73, 1), (4966519, 1)] : List FactorBlock).map factorBlockValue).prod) = 10876676611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_4966519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10876676611) ^ 5438338305 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10876676611) ^ 3625558870 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10876676611) ^ 2175335322 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10876676611) ^ 148995570 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 10876676611) ^ 2190 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_11129533489 : Nat.Prime 11129533489 := by
  apply lucas_primality 11129533489 (11 : ZMod 11129533489)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) = 11129533489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_653
      · exact prime_oneHundredThirtyFiveEC_13151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11129533489) ^ 5564766744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 3709844496 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 17043696 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 846288 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_11789483113 : Nat.Prime 11789483113 := by
  apply lucas_primality 11789483113 (5 : ZMod 11789483113)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (11, 1), (14885711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (11, 1), (14885711, 1)] : List FactorBlock).map factorBlockValue).prod) = 11789483113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_14885711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 11789483113) ^ 5894741556 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 11789483113) ^ 3929827704 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 11789483113) ^ 1071771192 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 11789483113) ^ 792 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_15289244417 : Nat.Prime 15289244417 := by
  apply lucas_primality 15289244417 (3 : ZMod 15289244417)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (59723611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (59723611, 1)] : List FactorBlock).map factorBlockValue).prod) = 15289244417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_59723611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 15289244417) ^ 7644622208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15289244417) ^ 256 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_19567268263 : Nat.Prime 19567268263 := by
  apply lucas_primality 19567268263 (3 : ZMod 19567268263)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (23, 1), (31, 1), (107, 1), (14249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (23, 1), (31, 1), (107, 1), (14249, 1)] : List FactorBlock).map factorBlockValue).prod) = 19567268263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_107
      · exact prime_oneHundredThirtyFiveEC_14249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 19567268263) ^ 9783634131 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19567268263) ^ 6522422754 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19567268263) ^ 850750794 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19567268263) ^ 631202202 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19567268263) ^ 182871666 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19567268263) ^ 1373238 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_20360887289 : Nat.Prime 20360887289 := by
  apply lucas_primality 20360887289 (3 : ZMod 20360887289)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (51941039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (51941039, 1)] : List FactorBlock).map factorBlockValue).prod) = 20360887289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_51941039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20360887289) ^ 10180443644 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 20360887289) ^ 2908698184 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 20360887289) ^ 392 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_173
      · exact prime_oneHundredThirtyFiveEC_1583
      · exact prime_oneHundredThirtyFiveEC_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_23534845667 : Nat.Prime 23534845667 := by
  apply lucas_primality 23534845667 (2 : ZMod 23534845667)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (287010313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (287010313, 1)] : List FactorBlock).map factorBlockValue).prod) = 23534845667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_287010313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 23534845667) ^ 11767422833 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 23534845667) ^ 574020626 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 23534845667) ^ 82 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_24701077187 : Nat.Prime 24701077187 := by
  apply lucas_primality 24701077187 (5 : ZMod 24701077187)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (227, 1), (397, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (227, 1), (397, 1), (7213, 1)] : List FactorBlock).map factorBlockValue).prod) = 24701077187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_227
      · exact prime_oneHundredThirtyFiveEC_397
      · exact prime_oneHundredThirtyFiveEC_7213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 24701077187) ^ 12350538593 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 24701077187) ^ 1300056694 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 24701077187) ^ 108815318 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 24701077187) ^ 62219338 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 24701077187) ^ 3424522 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_26258050361 : Nat.Prime 26258050361 := by
  apply lucas_primality 26258050361 (3 : ZMod 26258050361)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (73, 1), (8992483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (73, 1), (8992483, 1)] : List FactorBlock).map factorBlockValue).prod) = 26258050361 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_8992483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 26258050361) ^ 13129025180 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 26258050361) ^ 5251610072 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 26258050361) ^ 359699320 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 26258050361) ^ 2920 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_26800160419 : Nat.Prime 26800160419 := by
  apply lucas_primality 26800160419 (2 : ZMod 26800160419)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (23, 1), (2397581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (23, 1), (2397581, 1)] : List FactorBlock).map factorBlockValue).prod) = 26800160419 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_2397581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26800160419) ^ 13400080209 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26800160419) ^ 8933386806 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26800160419) ^ 1165224366 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26800160419) ^ 11178 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_28118094577 : Nat.Prime 28118094577 := by
  apply lucas_primality 28118094577 (5 : ZMod 28118094577)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (11, 1), (13, 1), (101, 1), (40559, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (11, 1), (13, 1), (101, 1), (40559, 1)] : List FactorBlock).map factorBlockValue).prod) = 28118094577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_101
      · exact prime_oneHundredThirtyFiveEC_40559
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 28118094577) ^ 14059047288 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 28118094577) ^ 9372698192 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 28118094577) ^ 2556190416 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 28118094577) ^ 2162930352 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 28118094577) ^ 278396976 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 28118094577) ^ 693264 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_32547740111 : Nat.Prime 32547740111 := by
  apply lucas_primality 32547740111 (17 : ZMod 32547740111)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (4273, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (4273, 1), (12487, 1)] : List FactorBlock).map factorBlockValue).prod) = 32547740111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_4273
      · exact prime_oneHundredThirtyFiveEC_12487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 32547740111) ^ 16273870055 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 32547740111) ^ 6509548022 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 32547740111) ^ 533569510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 32547740111) ^ 7617070 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 32547740111) ^ 2606530 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_39783239047 : Nat.Prime 39783239047 := by
  apply lucas_primality 39783239047 (3 : ZMod 39783239047)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (736726649, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (736726649, 1)] : List FactorBlock).map factorBlockValue).prod) = 39783239047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_736726649
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 39783239047) ^ 19891619523 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 39783239047) ^ 13261079682 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 39783239047) ^ 54 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_47221552583 : Nat.Prime 47221552583 := by
  apply lucas_primality 47221552583 (5 : ZMod 47221552583)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (3083, 1), (129803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (3083, 1), (129803, 1)] : List FactorBlock).map factorBlockValue).prod) = 47221552583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_59
      · exact prime_oneHundredThirtyFiveEC_3083
      · exact prime_oneHundredThirtyFiveEC_129803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 47221552583) ^ 23610776291 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 47221552583) ^ 800365298 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 47221552583) ^ 15316754 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 47221552583) ^ 363794 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_52586168543 : Nat.Prime 52586168543 := by
  apply lucas_primality 52586168543 (5 : ZMod 52586168543)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) = 52586168543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_1143177577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52586168543) ^ 26293084271 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 2286355154 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 46 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_58620243193 : Nat.Prime 58620243193 := by
  apply lucas_primality 58620243193 (5 : ZMod 58620243193)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (433, 1), (805843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (433, 1), (805843, 1)] : List FactorBlock).map factorBlockValue).prod) = 58620243193 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_433
      · exact prime_oneHundredThirtyFiveEC_805843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 58620243193) ^ 29310121596 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 58620243193) ^ 19540081064 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 58620243193) ^ 8374320456 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 58620243193) ^ 135381624 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 58620243193) ^ 72744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_61883305189 : Nat.Prime 61883305189 := by
  apply lucas_primality 61883305189 (2 : ZMod 61883305189)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (307, 1), (16797857, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (307, 1), (16797857, 1)] : List FactorBlock).map factorBlockValue).prod) = 61883305189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_307
      · exact prime_oneHundredThirtyFiveEC_16797857
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61883305189) ^ 30941652594 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 61883305189) ^ 20627768396 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 61883305189) ^ 201574284 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 61883305189) ^ 3684 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_62712523297 : Nat.Prime 62712523297 := by
  apply lucas_primality 62712523297 (10 : ZMod 62712523297)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 3), (71, 1), (457, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 3), (71, 1), (457, 1), (2237, 1)] : List FactorBlock).map factorBlockValue).prod) = 62712523297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_457
      · exact prime_oneHundredThirtyFiveEC_2237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 62712523297) ^ 31356261648 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 62712523297) ^ 20904174432 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 62712523297) ^ 883274976 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 62712523297) ^ 137226528 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 62712523297) ^ 28034208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_70736898679 : Nat.Prime 70736898679 := by
  apply lucas_primality 70736898679 (3 : ZMod 70736898679)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11789483113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11789483113, 1)] : List FactorBlock).map factorBlockValue).prod) = 70736898679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11789483113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 70736898679) ^ 35368449339 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 70736898679) ^ 23578966226 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 70736898679) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_83186137633 : Nat.Prime 83186137633 := by
  apply lucas_primality 83186137633 (10 : ZMod 83186137633)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (13, 1), (7817, 1), (8527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (13, 1), (7817, 1), (8527, 1)] : List FactorBlock).map factorBlockValue).prod) = 83186137633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_7817
      · exact prime_oneHundredThirtyFiveEC_8527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 83186137633) ^ 41593068816 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 83186137633) ^ 27728712544 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 83186137633) ^ 6398933664 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 83186137633) ^ 10641696 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 83186137633) ^ 9755616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_85915003129 : Nat.Prime 85915003129 := by
  apply lucas_primality 85915003129 (11 : ZMod 85915003129)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (8677, 1), (412561, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (8677, 1), (412561, 1)] : List FactorBlock).map factorBlockValue).prod) = 85915003129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_8677
      · exact prime_oneHundredThirtyFiveEC_412561
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 85915003129) ^ 42957501564 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 85915003129) ^ 28638334376 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 85915003129) ^ 9901464 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 85915003129) ^ 208248 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_86769594689 : Nat.Prime 86769594689 := by
  apply lucas_primality 86769594689 (3 : ZMod 86769594689)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (97, 1), (1996723, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (97, 1), (1996723, 1)] : List FactorBlock).map factorBlockValue).prod) = 86769594689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_97
      · exact prime_oneHundredThirtyFiveEC_1996723
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 86769594689) ^ 43384797344 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 86769594689) ^ 12395656384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 86769594689) ^ 894531904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 86769594689) ^ 43456 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_98426497831 : Nat.Prime 98426497831 := by
  apply lucas_primality 98426497831 (12 : ZMod 98426497831)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17, 1), (137, 1), (1408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17, 1), (137, 1), (1408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 98426497831 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_137
      · exact prime_oneHundredThirtyFiveEC_1408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 98426497831) ^ 49213248915 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 98426497831) ^ 32808832610 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 98426497831) ^ 19685299566 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 98426497831) ^ 5789793990 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 98426497831) ^ 718441590 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (12 : ZMod 98426497831) ^ 69870 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_106211754007 : Nat.Prime 106211754007 := by
  apply lucas_primality 106211754007 (5 : ZMod 106211754007)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (120383, 1), (147047, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (120383, 1), (147047, 1)] : List FactorBlock).map factorBlockValue).prod) = 106211754007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_120383
      · exact prime_oneHundredThirtyFiveEC_147047
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 106211754007) ^ 53105877003 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 106211754007) ^ 35403918002 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 106211754007) ^ 882282 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 106211754007) ^ 722298 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_120055286693 : Nat.Prime 120055286693 := by
  apply lucas_primality 120055286693 (2 : ZMod 120055286693)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) = 120055286693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_248048113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120055286693) ^ 60027643346 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 10914116972 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 484 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_131131181801 : Nat.Prime 131131181801 := by
  apply lucas_primality 131131181801 (6 : ZMod 131131181801)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (307, 1), (2135687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (307, 1), (2135687, 1)] : List FactorBlock).map factorBlockValue).prod) = 131131181801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_307
      · exact prime_oneHundredThirtyFiveEC_2135687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 131131181801) ^ 65565590900 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 131131181801) ^ 26226236360 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 131131181801) ^ 427137400 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 131131181801) ^ 61400 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_853
      · exact prime_oneHundredThirtyFiveEC_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_159942915893 : Nat.Prime 159942915893 := by
  apply lucas_primality 159942915893 (2 : ZMod 159942915893)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (503, 1), (79494491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (503, 1), (79494491, 1)] : List FactorBlock).map factorBlockValue).prod) = 159942915893 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_503
      · exact prime_oneHundredThirtyFiveEC_79494491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 159942915893) ^ 79971457946 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159942915893) ^ 317977964 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159942915893) ^ 2012 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_168708567463 : Nat.Prime 168708567463 := by
  apply lucas_primality 168708567463 (6 : ZMod 168708567463)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (28118094577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (28118094577, 1)] : List FactorBlock).map factorBlockValue).prod) = 168708567463 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_28118094577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 168708567463) ^ 84354283731 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 168708567463) ^ 56236189154 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 168708567463) ^ 6 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_177602339353 : Nat.Prime 177602339353 := by
  apply lucas_primality 177602339353 (5 : ZMod 177602339353)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (163, 1), (45399371, 1)] : List FactorBlock).map factorBlockValue).prod) = 177602339353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_163
      · exact prime_oneHundredThirtyFiveEC_45399371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 177602339353) ^ 88801169676 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 59200779784 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 1089584904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 177602339353) ^ 3912 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_190986192499 : Nat.Prime 190986192499 := by
  apply lucas_primality 190986192499 (2 : ZMod 190986192499)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (53, 1), (600585511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (53, 1), (600585511, 1)] : List FactorBlock).map factorBlockValue).prod) = 190986192499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_600585511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 190986192499) ^ 95493096249 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 190986192499) ^ 63662064166 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 190986192499) ^ 3603513066 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 190986192499) ^ 318 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_222133410637 : Nat.Prime 222133410637 := by
  apply lucas_primality 222133410637 (5 : ZMod 222133410637)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 222133410637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_373
      · exact prime_oneHundredThirtyFiveEC_3449
      · exact prime_oneHundredThirtyFiveEC_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222133410637) ^ 111066705318 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 74044470212 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 595531932 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 64405164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 15437724 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_235784242051 : Nat.Prime 235784242051 := by
  apply lucas_primality 235784242051 (46 : ZMod 235784242051)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (19, 1), (277, 1), (42667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (19, 1), (277, 1), (42667, 1)] : List FactorBlock).map factorBlockValue).prod) = 235784242051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_277
      · exact prime_oneHundredThirtyFiveEC_42667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (46 : ZMod 235784242051) ^ 117892121025 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 78594747350 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 47156848410 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 33683463150 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 12409696950 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 851206650 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (46 : ZMod 235784242051) ^ 5526150 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_238024728587 : Nat.Prime 238024728587 := by
  apply lucas_primality 238024728587 (5 : ZMod 238024728587)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (71, 1), (137, 1), (643961, 1)] : List FactorBlock).map factorBlockValue).prod) = 238024728587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_137
      · exact prime_oneHundredThirtyFiveEC_643961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 238024728587) ^ 119012364293 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 12527617294 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 3352460966 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 1737406778 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 238024728587) ^ 369626 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_339856636541 : Nat.Prime 339856636541 := by
  apply lucas_primality 339856636541 (10 : ZMod 339856636541)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (5449, 1), (3118523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (5449, 1), (3118523, 1)] : List FactorBlock).map factorBlockValue).prod) = 339856636541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_5449
      · exact prime_oneHundredThirtyFiveEC_3118523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 339856636541) ^ 169928318270 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 339856636541) ^ 67971327308 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 339856636541) ^ 62370460 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 339856636541) ^ 108980 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_414808869521 : Nat.Prime 414808869521 := by
  apply lucas_primality 414808869521 (6 : ZMod 414808869521)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (23, 1), (131, 1), (461, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (23, 1), (131, 1), (461, 1), (3733, 1)] : List FactorBlock).map factorBlockValue).prod) = 414808869521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_131
      · exact prime_oneHundredThirtyFiveEC_461
      · exact prime_oneHundredThirtyFiveEC_3733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 414808869521) ^ 207404434760 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 82961773904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 18035168240 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 3166479920 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 899802320 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 414808869521) ^ 111119440 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_419652079391 : Nat.Prime 419652079391 := by
  apply lucas_primality 419652079391 (19 : ZMod 419652079391)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13441, 1), (3122179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13441, 1), (3122179, 1)] : List FactorBlock).map factorBlockValue).prod) = 419652079391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13441
      · exact prime_oneHundredThirtyFiveEC_3122179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 419652079391) ^ 209826039695 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (19 : ZMod 419652079391) ^ 83930415878 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (19 : ZMod 419652079391) ^ 31221790 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (19 : ZMod 419652079391) ^ 134410 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_423473815627 : Nat.Prime 423473815627 := by
  apply lucas_primality 423473815627 (2 : ZMod 423473815627)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (271, 1), (277, 1), (389, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (271, 1), (277, 1), (389, 1), (2417, 1)] : List FactorBlock).map factorBlockValue).prod) = 423473815627 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_271
      · exact prime_oneHundredThirtyFiveEC_277
      · exact prime_oneHundredThirtyFiveEC_389
      · exact prime_oneHundredThirtyFiveEC_2417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 423473815627) ^ 211736907813 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 423473815627) ^ 141157938542 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 423473815627) ^ 1562634006 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 423473815627) ^ 1528786338 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 423473815627) ^ 1088621634 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 423473815627) ^ 175206378 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_514339818439 : Nat.Prime 514339818439 := by
  apply lucas_primality 514339818439 (3 : ZMod 514339818439)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (241, 1), (2939, 1), (3271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (241, 1), (2939, 1), (3271, 1)] : List FactorBlock).map factorBlockValue).prod) = 514339818439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_241
      · exact prime_oneHundredThirtyFiveEC_2939
      · exact prime_oneHundredThirtyFiveEC_3271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 514339818439) ^ 257169909219 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 514339818439) ^ 171446606146 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 514339818439) ^ 13901076174 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 514339818439) ^ 2134190118 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 514339818439) ^ 175005042 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 514339818439) ^ 157242378 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_829617739043 : Nat.Prime 829617739043 := by
  apply lucas_primality 829617739043 (2 : ZMod 829617739043)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (414808869521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (414808869521, 1)] : List FactorBlock).map factorBlockValue).prod) = 829617739043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_414808869521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 829617739043) ^ 414808869521 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 829617739043) ^ 2 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_840257611553 : Nat.Prime 840257611553 := by
  apply lucas_primality 840257611553 (3 : ZMod 840257611553)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (26258050361, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (26258050361, 1)] : List FactorBlock).map factorBlockValue).prod) = 840257611553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_26258050361
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 840257611553) ^ 420128805776 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 840257611553) ^ 32 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1262224075241 : Nat.Prime 1262224075241 := by
  apply lucas_primality 1262224075241 (3 : ZMod 1262224075241)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (419, 1), (2633, 1), (28603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (419, 1), (2633, 1), (28603, 1)] : List FactorBlock).map factorBlockValue).prod) = 1262224075241 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_419
      · exact prime_oneHundredThirtyFiveEC_2633
      · exact prime_oneHundredThirtyFiveEC_28603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1262224075241) ^ 631112037620 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1262224075241) ^ 252444815048 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1262224075241) ^ 3012467960 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1262224075241) ^ 479386280 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1262224075241) ^ 44129080 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1266812390323 : Nat.Prime 1266812390323 := by
  apply lucas_primality 1266812390323 (2 : ZMod 1266812390323)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (2693, 1), (26133853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (2693, 1), (26133853, 1)] : List FactorBlock).map factorBlockValue).prod) = 1266812390323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2693
      · exact prime_oneHundredThirtyFiveEC_26133853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1266812390323) ^ 633406195161 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1266812390323) ^ 422270796774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1266812390323) ^ 470409354 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1266812390323) ^ 48474 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1429468943351 : Nat.Prime 1429468943351 := by
  apply lucas_primality 1429468943351 (7 : ZMod 1429468943351)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (7, 1), (4084196981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (7, 1), (4084196981, 1)] : List FactorBlock).map factorBlockValue).prod) = 1429468943351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_4084196981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 1429468943351) ^ 714734471675 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1429468943351) ^ 285893788670 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1429468943351) ^ 204209849050 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1429468943351) ^ 350 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1497095305021 : Nat.Prime 1497095305021 := by
  apply lucas_primality 1497095305021 (6 : ZMod 1497095305021)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (7, 1), (1609, 1), (246151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (7, 1), (1609, 1), (246151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497095305021 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_1609
      · exact prime_oneHundredThirtyFiveEC_246151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1497095305021) ^ 748547652510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 1497095305021) ^ 499031768340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 1497095305021) ^ 299419061004 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 1497095305021) ^ 213870757860 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 1497095305021) ^ 930450780 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 1497095305021) ^ 6082020 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2082470272537 : Nat.Prime 2082470272537 := by
  apply lucas_primality 2082470272537 (10 : ZMod 2082470272537)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (86769594689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (86769594689, 1)] : List FactorBlock).map factorBlockValue).prod) = 2082470272537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_86769594689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (10 : ZMod 2082470272537) ^ 1041235136268 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2082470272537) ^ 694156757512 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2082470272537) ^ 24 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2115806147309 : Nat.Prime 2115806147309 := by
  apply lucas_primality 2115806147309 (3 : ZMod 2115806147309)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (10794929323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (10794929323, 1)] : List FactorBlock).map factorBlockValue).prod) = 2115806147309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_10794929323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2115806147309) ^ 1057903073654 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115806147309) ^ 302258021044 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2115806147309) ^ 196 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2201043108283 : Nat.Prime 2201043108283 := by
  apply lucas_primality 2201043108283 (2 : ZMod 2201043108283)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (479, 1), (557, 1), (631, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (479, 1), (557, 1), (631, 1), (2179, 1)] : List FactorBlock).map factorBlockValue).prod) = 2201043108283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_479
      · exact prime_oneHundredThirtyFiveEC_557
      · exact prime_oneHundredThirtyFiveEC_631
      · exact prime_oneHundredThirtyFiveEC_2179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2201043108283) ^ 1100521554141 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2201043108283) ^ 733681036094 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2201043108283) ^ 4595079558 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2201043108283) ^ 3951603426 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2201043108283) ^ 3488182422 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 2201043108283) ^ 1010116158 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2709058570633 : Nat.Prime 2709058570633 := by
  apply lucas_primality 2709058570633 (10 : ZMod 2709058570633)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (47, 1), (3331, 1), (80111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (47, 1), (3331, 1), (80111, 1)] : List FactorBlock).map factorBlockValue).prod) = 2709058570633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_3331
      · exact prime_oneHundredThirtyFiveEC_80111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2709058570633) ^ 1354529285316 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2709058570633) ^ 903019523544 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2709058570633) ^ 57639544056 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2709058570633) ^ 813286872 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 2709058570633) ^ 33816312 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3589483176079 : Nat.Prime 3589483176079 := by
  apply lucas_primality 3589483176079 (6 : ZMod 3589483176079)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (167, 1), (1901, 1), (99181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (167, 1), (1901, 1), (99181, 1)] : List FactorBlock).map factorBlockValue).prod) = 3589483176079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_167
      · exact prime_oneHundredThirtyFiveEC_1901
      · exact prime_oneHundredThirtyFiveEC_99181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3589483176079) ^ 1794741588039 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 3589483176079) ^ 1196494392026 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 3589483176079) ^ 188920167162 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 3589483176079) ^ 21493911234 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 3589483176079) ^ 1888207878 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 3589483176079) ^ 36191238 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3797081613103 : Nat.Prime 3797081613103 := by
  apply lucas_primality 3797081613103 (5 : ZMod 3797081613103)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (733813, 1), (862409, 1)] : List FactorBlock).map factorBlockValue).prod) = 3797081613103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_733813
      · exact prime_oneHundredThirtyFiveEC_862409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 3797081613103) ^ 1898540806551 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 1265693871034 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 5174454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 3797081613103) ^ 4402878 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3828928573363 : Nat.Prime 3828928573363 := by
  apply lucas_primality 3828928573363 (11 : ZMod 3828928573363)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (353, 1), (1807803859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (353, 1), (1807803859, 1)] : List FactorBlock).map factorBlockValue).prod) = 3828928573363 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_353
      · exact prime_oneHundredThirtyFiveEC_1807803859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 3828928573363) ^ 1914464286681 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828928573363) ^ 1276309524454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828928573363) ^ 10846823154 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 3828928573363) ^ 2118 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4289449148729 : Nat.Prime 4289449148729 := by
  apply lucas_primality 4289449148729 (3 : ZMod 4289449148729)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (773, 1), (36507193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (773, 1), (36507193, 1)] : List FactorBlock).map factorBlockValue).prod) = 4289449148729 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_773
      · exact prime_oneHundredThirtyFiveEC_36507193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 4289449148729) ^ 2144724574364 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4289449148729) ^ 225760481512 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4289449148729) ^ 5549093336 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4289449148729) ^ 117496 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6271489433791 : Nat.Prime 6271489433791 := by
  apply lucas_primality 6271489433791 (3 : ZMod 6271489433791)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (101, 1), (103, 1), (109, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (101, 1), (103, 1), (109, 1), (8779, 1)] : List FactorBlock).map factorBlockValue).prod) = 6271489433791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_101
      · exact prime_oneHundredThirtyFiveEC_103
      · exact prime_oneHundredThirtyFiveEC_109
      · exact prime_oneHundredThirtyFiveEC_8779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6271489433791) ^ 3135744716895 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 2090496477930 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 1254297886758 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 895927061970 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 62093954790 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 60888246930 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 57536600310 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 6271489433791) ^ 714374010 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7104093574121 : Nat.Prime 7104093574121 := by
  apply lucas_primality 7104093574121 (3 : ZMod 7104093574121)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (177602339353, 1)] : List FactorBlock).map factorBlockValue).prod) = 7104093574121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_177602339353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 7104093574121) ^ 3552046787060 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 1420818714824 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7104093574121) ^ 40 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_8617969345417 : Nat.Prime 8617969345417 := by
  apply lucas_primality 8617969345417 (10 : ZMod 8617969345417)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (239, 1), (1502435381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (239, 1), (1502435381, 1)] : List FactorBlock).map factorBlockValue).prod) = 8617969345417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_239
      · exact prime_oneHundredThirtyFiveEC_1502435381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 8617969345417) ^ 4308984672708 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 8617969345417) ^ 2872656448472 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 8617969345417) ^ 36058449144 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 8617969345417) ^ 5736 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_11976257000707 : Nat.Prime 11976257000707 := by
  apply lucas_primality 11976257000707 (2 : ZMod 11976257000707)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (263, 1), (3313, 1), (2290829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (263, 1), (3313, 1), (2290829, 1)] : List FactorBlock).map factorBlockValue).prod) = 11976257000707 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_263
      · exact prime_oneHundredThirtyFiveEC_3313
      · exact prime_oneHundredThirtyFiveEC_2290829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11976257000707) ^ 5988128500353 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11976257000707) ^ 3992085666902 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11976257000707) ^ 45537098862 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11976257000707) ^ 3614928162 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11976257000707) ^ 5227914 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_12390650303663 : Nat.Prime 12390650303663 := by
  apply lucas_primality 12390650303663 (5 : ZMod 12390650303663)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (587, 1), (23297, 1), (453029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (587, 1), (23297, 1), (453029, 1)] : List FactorBlock).map factorBlockValue).prod) = 12390650303663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_587
      · exact prime_oneHundredThirtyFiveEC_23297
      · exact prime_oneHundredThirtyFiveEC_453029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 12390650303663) ^ 6195325151831 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 12390650303663) ^ 21108433226 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 12390650303663) ^ 531856046 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 12390650303663) ^ 27350678 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_14147054523061 : Nat.Prime 14147054523061 := by
  apply lucas_primality 14147054523061 (7 : ZMod 14147054523061)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (235784242051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (235784242051, 1)] : List FactorBlock).map factorBlockValue).prod) = 14147054523061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_235784242051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 14147054523061) ^ 7073527261530 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 14147054523061) ^ 4715684841020 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 14147054523061) ^ 2829410904612 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 14147054523061) ^ 60 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_6427
      · exact prime_oneHundredThirtyFiveEC_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_16754089251811 : Nat.Prime 16754089251811 := by
  apply lucas_primality 16754089251811 (2 : ZMod 16754089251811)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (4817, 1), (115937231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (4817, 1), (115937231, 1)] : List FactorBlock).map factorBlockValue).prod) = 16754089251811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_4817
      · exact prime_oneHundredThirtyFiveEC_115937231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 16754089251811) ^ 8377044625905 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 16754089251811) ^ 5584696417270 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 16754089251811) ^ 3350817850362 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 16754089251811) ^ 3478116930 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 16754089251811) ^ 144510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_18406275161867 : Nat.Prime 18406275161867 := by
  apply lucas_primality 18406275161867 (2 : ZMod 18406275161867)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 2), (853, 1), (1151, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 2), (853, 1), (1151, 1), (1759, 1)] : List FactorBlock).map factorBlockValue).prod) = 18406275161867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_853
      · exact prime_oneHundredThirtyFiveEC_1151
      · exact prime_oneHundredThirtyFiveEC_1759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 18406275161867) ^ 9203137580933 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 18406275161867) ^ 252140755642 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 18406275161867) ^ 21578282722 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 18406275161867) ^ 15991550966 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 18406275161867) ^ 10464056374 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_23580678731417 : Nat.Prime 23580678731417 := by
  apply lucas_primality 23580678731417 (3 : ZMod 23580678731417)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (288689, 1), (10210243, 1)] : List FactorBlock).map factorBlockValue).prod) = 23580678731417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_288689
      · exact prime_oneHundredThirtyFiveEC_10210243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 23580678731417) ^ 11790339365708 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 81681944 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 23580678731417) ^ 2309512 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_26851715585323 : Nat.Prime 26851715585323 := by
  apply lucas_primality 26851715585323 (2 : ZMod 26851715585323)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (24337, 1), (89833, 1)] : List FactorBlock).map factorBlockValue).prod) = 26851715585323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_89
      · exact prime_oneHundredThirtyFiveEC_24337
      · exact prime_oneHundredThirtyFiveEC_89833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 26851715585323) ^ 13425857792661 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 8950571861774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1167465895014 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 301704669498 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 1103328906 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 26851715585323) ^ 298907034 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_34608885102271 : Nat.Prime 34608885102271 := by
  apply lucas_primality 34608885102271 (3 : ZMod 34608885102271)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (229, 1), (1679227807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (229, 1), (1679227807, 1)] : List FactorBlock).map factorBlockValue).prod) = 34608885102271 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_229
      · exact prime_oneHundredThirtyFiveEC_1679227807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34608885102271) ^ 17304442551135 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 34608885102271) ^ 11536295034090 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 34608885102271) ^ 6921777020454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 34608885102271) ^ 151130502630 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 34608885102271) ^ 20610 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_42224929795753 : Nat.Prime 42224929795753 := by
  apply lucas_primality 42224929795753 (5 : ZMod 42224929795753)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (159942915893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (159942915893, 1)] : List FactorBlock).map factorBlockValue).prod) = 42224929795753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_159942915893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 42224929795753) ^ 21112464897876 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 42224929795753) ^ 14074976598584 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 42224929795753) ^ 3838629981432 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 42224929795753) ^ 264 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_46933841240063 : Nat.Prime 46933841240063 := by
  apply lucas_primality 46933841240063 (5 : ZMod 46933841240063)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (103, 1), (32547740111, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (103, 1), (32547740111, 1)] : List FactorBlock).map factorBlockValue).prod) = 46933841240063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_103
      · exact prime_oneHundredThirtyFiveEC_32547740111
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 46933841240063) ^ 23466920620031 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 46933841240063) ^ 6704834462866 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 46933841240063) ^ 455668361554 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 46933841240063) ^ 1442 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_47061672383657 : Nat.Prime 47061672383657 := by
  apply lucas_primality 47061672383657 (3 : ZMod 47061672383657)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) = 47061672383657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_120055286693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47061672383657) ^ 23530836191828 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 6723096054808 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 392 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_47506380087479 : Nat.Prime 47506380087479 := by
  apply lucas_primality 47506380087479 (11 : ZMod 47506380087479)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (32911, 1), (55518473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (32911, 1), (55518473, 1)] : List FactorBlock).map factorBlockValue).prod) = 47506380087479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_32911
      · exact prime_oneHundredThirtyFiveEC_55518473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 47506380087479) ^ 23753190043739 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 47506380087479) ^ 3654336929806 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 47506380087479) ^ 1443480298 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 47506380087479) ^ 855686 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_50762704307089 : Nat.Prime 50762704307089 := by
  apply lucas_primality 50762704307089 (7 : ZMod 50762704307089)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (73, 1), (167, 1), (601, 1), (144341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (73, 1), (167, 1), (601, 1), (144341, 1)] : List FactorBlock).map factorBlockValue).prod) = 50762704307089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_167
      · exact prime_oneHundredThirtyFiveEC_601
      · exact prime_oneHundredThirtyFiveEC_144341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 50762704307089) ^ 25381352153544 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 50762704307089) ^ 16920901435696 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 50762704307089) ^ 695379511056 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 50762704307089) ^ 303968289264 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 50762704307089) ^ 84463734288 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 50762704307089) ^ 351685968 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_55463448789821 : Nat.Prime 55463448789821 := by
  apply lucas_primality 55463448789821 (2 : ZMod 55463448789821)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (367, 1), (7556328173, 1)] : List FactorBlock).map factorBlockValue).prod) = 55463448789821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_367
      · exact prime_oneHundredThirtyFiveEC_7556328173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 55463448789821) ^ 27731724394910 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 11092689757964 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 151126563460 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 55463448789821) ^ 7340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_66569056940209 : Nat.Prime 66569056940209 := by
  apply lucas_primality 66569056940209 (11 : ZMod 66569056940209)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (12503, 1), (110921807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (12503, 1), (110921807, 1)] : List FactorBlock).map factorBlockValue).prod) = 66569056940209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_12503
      · exact prime_oneHundredThirtyFiveEC_110921807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 66569056940209) ^ 33284528470104 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 66569056940209) ^ 22189685646736 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 66569056940209) ^ 5324246736 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 66569056940209) ^ 600144 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_78894590925509 : Nat.Prime 78894590925509 := by
  apply lucas_primality 78894590925509 (2 : ZMod 78894590925509)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (419652079391, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (419652079391, 1)] : List FactorBlock).map factorBlockValue).prod) = 78894590925509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_419652079391
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 78894590925509) ^ 39447295462754 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 78894590925509) ^ 1678608317564 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 78894590925509) ^ 188 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_86179693454171 : Nat.Prime 86179693454171 := by
  apply lucas_primality 86179693454171 (2 : ZMod 86179693454171)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (8617969345417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (8617969345417, 1)] : List FactorBlock).map factorBlockValue).prod) = 86179693454171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_8617969345417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 86179693454171) ^ 43089846727085 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 86179693454171) ^ 17235938690834 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 86179693454171) ^ 10 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_173
      · exact prime_oneHundredThirtyFiveEC_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_110926897579643 : Nat.Prime 110926897579643 := by
  apply lucas_primality 110926897579643 (2 : ZMod 110926897579643)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (55463448789821, 1)] : List FactorBlock).map factorBlockValue).prod) = 110926897579643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_55463448789821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 110926897579643) ^ 55463448789821 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 110926897579643) ^ 2 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_317
      · exact prime_oneHundredThirtyFiveEC_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_158653223449549 : Nat.Prime 158653223449549 := by
  apply lucas_primality 158653223449549 (2 : ZMod 158653223449549)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (73, 1), (823, 1), (1427, 1), (154213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (73, 1), (823, 1), (1427, 1), (154213, 1)] : List FactorBlock).map factorBlockValue).prod) = 158653223449549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_823
      · exact prime_oneHundredThirtyFiveEC_1427
      · exact prime_oneHundredThirtyFiveEC_154213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 158653223449549) ^ 79326611724774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 158653223449549) ^ 52884407816516 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 158653223449549) ^ 2173331828076 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 158653223449549) ^ 192774269076 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 158653223449549) ^ 111179553924 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 158653223449549) ^ 1028792796 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_185625335787497 : Nat.Prime 185625335787497 := by
  apply lucas_primality 185625335787497 (3 : ZMod 185625335787497)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (367, 1), (1229, 1), (4676669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (367, 1), (1229, 1), (4676669, 1)] : List FactorBlock).map factorBlockValue).prod) = 185625335787497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_367
      · exact prime_oneHundredThirtyFiveEC_1229
      · exact prime_oneHundredThirtyFiveEC_4676669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 185625335787497) ^ 92812667893748 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 185625335787497) ^ 16875030526136 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 185625335787497) ^ 505791105688 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 185625335787497) ^ 151037702024 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 185625335787497) ^ 39691784 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_243521692501993 : Nat.Prime 243521692501993 := by
  apply lucas_primality 243521692501993 (5 : ZMod 243521692501993)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (29, 1), (388363, 1), (900929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (29, 1), (388363, 1), (900929, 1)] : List FactorBlock).map factorBlockValue).prod) = 243521692501993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_388363
      · exact prime_oneHundredThirtyFiveEC_900929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 243521692501993) ^ 121760846250996 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 243521692501993) ^ 81173897500664 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 243521692501993) ^ 8397299741448 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 243521692501993) ^ 627046584 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 243521692501993) ^ 270300648 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_273308408322643 : Nat.Prime 273308408322643 := by
  apply lucas_primality 273308408322643 (3 : ZMod 273308408322643)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) = 273308408322643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_1109
      · exact prime_oneHundredThirtyFiveEC_5273
      · exact prime_oneHundredThirtyFiveEC_33721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 273308408322643) ^ 136654204161321 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 91102802774214 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 39044058331806 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 24846218938422 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 246445814538 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 51831672354 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 8104991202 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_639989122926467 : Nat.Prime 639989122926467 := by
  apply lucas_primality 639989122926467 (2 : ZMod 639989122926467)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (137, 1), (55921, 1), (41768329, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (137, 1), (55921, 1), (41768329, 1)] : List FactorBlock).map factorBlockValue).prod) = 639989122926467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_137
      · exact prime_oneHundredThirtyFiveEC_55921
      · exact prime_oneHundredThirtyFiveEC_41768329
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 639989122926467) ^ 319994561463233 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 639989122926467) ^ 4671453452018 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 639989122926467) ^ 11444522146 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 639989122926467) ^ 15322354 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_666296641929871 : Nat.Prime 666296641929871 := by
  apply lucas_primality 666296641929871 (3 : ZMod 666296641929871)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (7, 2), (26573, 1), (631751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (7, 2), (26573, 1), (631751, 1)] : List FactorBlock).map factorBlockValue).prod) = 666296641929871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_26573
      · exact prime_oneHundredThirtyFiveEC_631751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 666296641929871) ^ 333148320964935 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 666296641929871) ^ 222098880643290 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 666296641929871) ^ 133259328385974 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 666296641929871) ^ 95185234561410 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 666296641929871) ^ 25074197190 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 666296641929871) ^ 1054682370 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_740017763996981 : Nat.Prime 740017763996981 := by
  apply lucas_primality 740017763996981 (2 : ZMod 740017763996981)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (547, 1), (9663329381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (547, 1), (9663329381, 1)] : List FactorBlock).map factorBlockValue).prod) = 740017763996981 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_547
      · exact prime_oneHundredThirtyFiveEC_9663329381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 740017763996981) ^ 370008881998490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 740017763996981) ^ 148003552799396 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 740017763996981) ^ 105716823428140 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 740017763996981) ^ 1352866113340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 740017763996981) ^ 76580 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_793062569613863 : Nat.Prime 793062569613863 := by
  apply lucas_primality 793062569613863 (5 : ZMod 793062569613863)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (6323, 1), (62712523297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (6323, 1), (62712523297, 1)] : List FactorBlock).map factorBlockValue).prod) = 793062569613863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_6323
      · exact prime_oneHundredThirtyFiveEC_62712523297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 793062569613863) ^ 396531284806931 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 793062569613863) ^ 125425046594 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 793062569613863) ^ 12646 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_938684030126243 : Nat.Prime 938684030126243 := by
  apply lucas_primality 938684030126243 (2 : ZMod 938684030126243)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1381, 1), (339856636541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1381, 1), (339856636541, 1)] : List FactorBlock).map factorBlockValue).prod) = 938684030126243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_1381
      · exact prime_oneHundredThirtyFiveEC_339856636541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 938684030126243) ^ 469342015063121 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 938684030126243) ^ 679713273082 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 938684030126243) ^ 2762 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_977965682448817 : Nat.Prime 977965682448817 := by
  apply lucas_primality 977965682448817 (5 : ZMod 977965682448817)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (98426497831, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (98426497831, 1)] : List FactorBlock).map factorBlockValue).prod) = 977965682448817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_98426497831
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 977965682448817) ^ 488982841224408 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 977965682448817) ^ 325988560816272 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 977965682448817) ^ 42520247062992 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 977965682448817) ^ 9936 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1094647771778333 : Nat.Prime 1094647771778333 := by
  apply lucas_primality 1094647771778333 (2 : ZMod 1094647771778333)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (337, 1), (24821, 1), (1128151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (337, 1), (24821, 1), (1128151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1094647771778333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_337
      · exact prime_oneHundredThirtyFiveEC_24821
      · exact prime_oneHundredThirtyFiveEC_1128151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1094647771778333) ^ 547323885889166 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094647771778333) ^ 37746474888908 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094647771778333) ^ 3248212972636 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094647771778333) ^ 44101678892 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1094647771778333) ^ 970302532 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1353881570594633 : Nat.Prime 1353881570594633 := by
  apply lucas_primality 1353881570594633 (3 : ZMod 1353881570594633)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2381, 1), (2801, 1), (25375709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2381, 1), (2801, 1), (25375709, 1)] : List FactorBlock).map factorBlockValue).prod) = 1353881570594633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_2381
      · exact prime_oneHundredThirtyFiveEC_2801
      · exact prime_oneHundredThirtyFiveEC_25375709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1353881570594633) ^ 676940785297316 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 568618887272 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 483356505032 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1353881570594633) ^ 53353448 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_197
      · exact prime_oneHundredThirtyFiveEC_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1552976566115003 : Nat.Prime 1552976566115003 := by
  apply lucas_primality 1552976566115003 (2 : ZMod 1552976566115003)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (110926897579643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1552976566115003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_110926897579643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1552976566115003) ^ 776488283057501 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 221853795159286 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1552976566115003) ^ 14 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1679837835044261 : Nat.Prime 1679837835044261 := by
  apply lucas_primality 1679837835044261 (2 : ZMod 1679837835044261)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (23, 1), (43, 1), (61, 1), (1392230797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (23, 1), (43, 1), (61, 1), (1392230797, 1)] : List FactorBlock).map factorBlockValue).prod) = 1679837835044261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_43
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_1392230797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1679837835044261) ^ 839918917522130 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679837835044261) ^ 335967567008852 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679837835044261) ^ 73036427610620 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679837835044261) ^ 39065996163820 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679837835044261) ^ 27538325164660 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1679837835044261) ^ 1206580 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2836629724719233 : Nat.Prime 2836629724719233 := by
  apply lucas_primality 2836629724719233 (3 : ZMod 2836629724719233)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (13, 2), (131131181801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (13, 2), (131131181801, 1)] : List FactorBlock).map factorBlockValue).prod) = 2836629724719233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_131131181801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2836629724719233) ^ 1418314862359616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2836629724719233) ^ 218202286516864 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2836629724719233) ^ 21632 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4564756240143017 : Nat.Prime 4564756240143017 := by
  apply lucas_primality 4564756240143017 (3 : ZMod 4564756240143017)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (18406275161867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (18406275161867, 1)] : List FactorBlock).map factorBlockValue).prod) = 4564756240143017 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_18406275161867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4564756240143017) ^ 2282378120071508 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4564756240143017) ^ 147250201294936 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4564756240143017) ^ 248 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4573879583189381 : Nat.Prime 4573879583189381 := by
  apply lucas_primality 4573879583189381 (2 : ZMod 4573879583189381)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (29, 1), (167, 1), (47221552583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (29, 1), (167, 1), (47221552583, 1)] : List FactorBlock).map factorBlockValue).prod) = 4573879583189381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_167
      · exact prime_oneHundredThirtyFiveEC_47221552583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4573879583189381) ^ 2286939791594690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 4573879583189381) ^ 914775916637876 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 4573879583189381) ^ 157719985627220 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 4573879583189381) ^ 27388500498140 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 4573879583189381) ^ 96860 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6248811431728417 : Nat.Prime 6248811431728417 := by
  apply lucas_primality 6248811431728417 (5 : ZMod 6248811431728417)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (17, 1), (3828928573363, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (17, 1), (3828928573363, 1)] : List FactorBlock).map factorBlockValue).prod) = 6248811431728417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_3828928573363
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6248811431728417) ^ 3124405715864208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6248811431728417) ^ 2082937143909472 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6248811431728417) ^ 367577143042848 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 6248811431728417) ^ 1632 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6920297186628619 : Nat.Prime 6920297186628619 := by
  apply lucas_primality 6920297186628619 (2 : ZMod 6920297186628619)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (71, 1), (108709, 1), (3831643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (71, 1), (108709, 1), (3831643, 1)] : List FactorBlock).map factorBlockValue).prod) = 6920297186628619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_108709
      · exact prime_oneHundredThirtyFiveEC_3831643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6920297186628619) ^ 3460148593314309 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 6920297186628619) ^ 2306765728876206 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 6920297186628619) ^ 532330552817586 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 6920297186628619) ^ 97468974459558 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 6920297186628619) ^ 63658916802 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 6920297186628619) ^ 1806091326 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7354493853937381 : Nat.Prime 7354493853937381 := by
  apply lucas_primality 7354493853937381 (18 : ZMod 7354493853937381)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 1), (67, 1), (1979, 1), (2081, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 1), (67, 1), (1979, 1), (2081, 1), (16453, 1)] : List FactorBlock).map factorBlockValue).prod) = 7354493853937381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_67
      · exact prime_oneHundredThirtyFiveEC_1979
      · exact prime_oneHundredThirtyFiveEC_2081
      · exact prime_oneHundredThirtyFiveEC_16453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 7354493853937381) ^ 3677246926968690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 2451497951312460 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 1470898770787476 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 109768564984140 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 3716267738220 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 3534115258980 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (18 : ZMod 7354493853937381) ^ 447000173460 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7580238420295529 : Nat.Prime 7580238420295529 := by
  apply lucas_primality 7580238420295529 (3 : ZMod 7580238420295529)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (79, 1), (827, 1), (1103, 1), (1011443, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (79, 1), (827, 1), (1103, 1), (1011443, 1)] : List FactorBlock).map factorBlockValue).prod) = 7580238420295529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_79
      · exact prime_oneHundredThirtyFiveEC_827
      · exact prime_oneHundredThirtyFiveEC_1103
      · exact prime_oneHundredThirtyFiveEC_1011443
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 7580238420295529) ^ 3790119210147764 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7580238420295529) ^ 583095263099656 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7580238420295529) ^ 95952385067032 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7580238420295529) ^ 9165947303864 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7580238420295529) ^ 6872382973976 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 7580238420295529) ^ 7494479096 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_10518021020214751 : Nat.Prime 10518021020214751 := by
  apply lucas_primality 10518021020214751 (6 : ZMod 10518021020214751)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (7, 1), (1259, 1), (1591288781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (7, 1), (1259, 1), (1591288781, 1)] : List FactorBlock).map factorBlockValue).prod) = 10518021020214751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_1259
      · exact prime_oneHundredThirtyFiveEC_1591288781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 10518021020214751) ^ 5259010510107375 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 10518021020214751) ^ 3506007006738250 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 10518021020214751) ^ 2103604204042950 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 10518021020214751) ^ 1502574431459250 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 10518021020214751) ^ 8354266100250 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 10518021020214751) ^ 6609750 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_12415654507405111 : Nat.Prime 12415654507405111 := by
  apply lucas_primality 12415654507405111 (3 : ZMod 12415654507405111)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (242057, 1), (131518657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (242057, 1), (131518657, 1)] : List FactorBlock).map factorBlockValue).prod) = 12415654507405111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_242057
      · exact prime_oneHundredThirtyFiveEC_131518657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12415654507405111) ^ 6207827253702555 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 12415654507405111) ^ 4138551502468370 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 12415654507405111) ^ 2483130901481022 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 12415654507405111) ^ 955050346723470 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 12415654507405111) ^ 51292276230 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 12415654507405111) ^ 94402230 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_17410293215602999 : Nat.Prime 17410293215602999 := by
  apply lucas_primality 17410293215602999 (6 : ZMod 17410293215602999)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (1229, 1), (85193, 1), (1458631, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (1229, 1), (85193, 1), (1458631, 1)] : List FactorBlock).map factorBlockValue).prod) = 17410293215602999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_1229
      · exact prime_oneHundredThirtyFiveEC_85193
      · exact prime_oneHundredThirtyFiveEC_1458631
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 17410293215602999) ^ 8705146607801499 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 17410293215602999) ^ 5803431071867666 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 17410293215602999) ^ 916331221873842 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 17410293215602999) ^ 14166227189262 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 17410293215602999) ^ 204362954886 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 17410293215602999) ^ 11936050458 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_20943565178693489 : Nat.Prime 20943565178693489 := by
  apply lucas_primality 20943565178693489 (3 : ZMod 20943565178693489)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (31, 1), (42224929795753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (31, 1), (42224929795753, 1)] : List FactorBlock).map factorBlockValue).prod) = 20943565178693489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_42224929795753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 20943565178693489) ^ 10471782589346744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 20943565178693489) ^ 675598876732048 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 20943565178693489) ^ 496 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_30669297629253853 : Nat.Prime 30669297629253853 := by
  apply lucas_primality 30669297629253853 (6 : ZMod 30669297629253853)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (179, 1), (11701, 1), (1220243699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (179, 1), (11701, 1), (1220243699, 1)] : List FactorBlock).map factorBlockValue).prod) = 30669297629253853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_179
      · exact prime_oneHundredThirtyFiveEC_11701
      · exact prime_oneHundredThirtyFiveEC_1220243699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 30669297629253853) ^ 15334648814626926 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 30669297629253853) ^ 10223099209751284 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 30669297629253853) ^ 171336858263988 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 30669297629253853) ^ 2621083465452 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 30669297629253853) ^ 25133748 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_40377390718990079 : Nat.Prime 40377390718990079 := by
  apply lucas_primality 40377390718990079 (17 : ZMod 40377390718990079)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1552976566115003, 1)] : List FactorBlock).map factorBlockValue).prod) = 40377390718990079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_1552976566115003
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 40377390718990079) ^ 20188695359495039 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 3105953132230006 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (17 : ZMod 40377390718990079) ^ 26 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_57277827640317811 : Nat.Prime 57277827640317811 := by
  apply lucas_primality 57277827640317811 (7 : ZMod 57277827640317811)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (179, 1), (26497, 1), (402546029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (179, 1), (26497, 1), (402546029, 1)] : List FactorBlock).map factorBlockValue).prod) = 57277827640317811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_179
      · exact prime_oneHundredThirtyFiveEC_26497
      · exact prime_oneHundredThirtyFiveEC_402546029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 57277827640317811) ^ 28638913820158905 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 57277827640317811) ^ 19092609213439270 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 57277827640317811) ^ 11455565528063562 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 57277827640317811) ^ 319987863912390 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 57277827640317811) ^ 2161672175730 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 57277827640317811) ^ 142288890 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_58915680555620989 : Nat.Prime 58915680555620989 := by
  apply lucas_primality 58915680555620989 (2 : ZMod 58915680555620989)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (59, 1), (75619, 1), (33346693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (59, 1), (75619, 1), (33346693, 1)] : List FactorBlock).map factorBlockValue).prod) = 58915680555620989 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_59
      · exact prime_oneHundredThirtyFiveEC_75619
      · exact prime_oneHundredThirtyFiveEC_33346693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 58915680555620989) ^ 29457840277810494 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 58915680555620989) ^ 19638560185206996 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 58915680555620989) ^ 5355970959601908 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 58915680555620989) ^ 998570856874932 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 58915680555620989) ^ 779112135252 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 58915680555620989) ^ 1766762316 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_99925883771346739 : Nat.Prime 99925883771346739 := by
  apply lucas_primality 99925883771346739 (3 : ZMod 99925883771346739)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (793062569613863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (793062569613863, 1)] : List FactorBlock).map factorBlockValue).prod) = 99925883771346739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_793062569613863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 99925883771346739) ^ 49962941885673369 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 99925883771346739) ^ 33308627923782246 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 99925883771346739) ^ 14275126253049534 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 99925883771346739) ^ 126 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_103142820044894053 : Nat.Prime 103142820044894053 := by
  apply lucas_primality 103142820044894053 (2 : ZMod 103142820044894053)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (53, 1), (89, 1), (349, 1), (1553, 1), (146173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (53, 1), (89, 1), (349, 1), (1553, 1), (146173, 1)] : List FactorBlock).map factorBlockValue).prod) = 103142820044894053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_89
      · exact prime_oneHundredThirtyFiveEC_349
      · exact prime_oneHundredThirtyFiveEC_1553
      · exact prime_oneHundredThirtyFiveEC_146173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 103142820044894053) ^ 51571410022447026 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 34380940014964684 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 4484470436734524 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 1946090944243284 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 1158908090392068 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 295538166317748 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 66415209301284 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 103142820044894053) ^ 705621558324 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_117351072154346377 : Nat.Prime 117351072154346377 := by
  apply lucas_primality 117351072154346377 (5 : ZMod 117351072154346377)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (2311, 1), (2115806147309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (2311, 1), (2115806147309, 1)] : List FactorBlock).map factorBlockValue).prod) = 117351072154346377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2311
      · exact prime_oneHundredThirtyFiveEC_2115806147309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 117351072154346377) ^ 58675536077173188 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 117351072154346377) ^ 39117024051448792 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 117351072154346377) ^ 50779347535416 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 117351072154346377) ^ 55464 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_119037976864322863 : Nat.Prime 119037976864322863 := by
  apply lucas_primality 119037976864322863 (3 : ZMod 119037976864322863)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 1), (639989122926467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 1), (639989122926467, 1)] : List FactorBlock).map factorBlockValue).prod) = 119037976864322863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_639989122926467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 119037976864322863) ^ 59518988432161431 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 119037976864322863) ^ 39679325621440954 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 119037976864322863) ^ 3839934737558802 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 119037976864322863) ^ 186 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_192939564814238843 : Nat.Prime 192939564814238843 := by
  apply lucas_primality 192939564814238843 (2 : ZMod 192939564814238843)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (37, 1), (73, 1), (80629, 1), (23314271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (37, 1), (73, 1), (80629, 1), (23314271, 1)] : List FactorBlock).map factorBlockValue).prod) = 192939564814238843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_37
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_80629
      · exact prime_oneHundredThirtyFiveEC_23314271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 192939564814238843) ^ 96469782407119421 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 192939564814238843) ^ 10154713937591518 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 192939564814238843) ^ 5214582832817266 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 192939564814238843) ^ 2643007737181354 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 192939564814238843) ^ 2392930146898 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 192939564814238843) ^ 8275599302 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_393934581260993837 : Nat.Prime 393934581260993837 := by
  apply lucas_primality 393934581260993837 (2 : ZMod 393934581260993837)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (12329, 1), (113363, 1), (1438033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (12329, 1), (113363, 1), (1438033, 1)] : List FactorBlock).map factorBlockValue).prod) = 393934581260993837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_12329
      · exact prime_oneHundredThirtyFiveEC_113363
      · exact prime_oneHundredThirtyFiveEC_1438033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 393934581260993837) ^ 196967290630496918 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 393934581260993837) ^ 56276368751570548 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 393934581260993837) ^ 31951868055884 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 393934581260993837) ^ 3474983735972 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 393934581260993837) ^ 273939875692 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_419996061740133023 : Nat.Prime 419996061740133023 := by
  apply lucas_primality 419996061740133023 (5 : ZMod 419996061740133023)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (882253, 1), (238024728587, 1)] : List FactorBlock).map factorBlockValue).prod) = 419996061740133023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_882253
      · exact prime_oneHundredThirtyFiveEC_238024728587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 419996061740133023) ^ 209998030870066511 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 476049457174 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 419996061740133023) ^ 1764506 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_595729980056158291 : Nat.Prime 595729980056158291 := by
  apply lucas_primality 595729980056158291 (2 : ZMod 595729980056158291)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (283, 1), (58620243193, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (19, 1), (283, 1), (58620243193, 1)] : List FactorBlock).map factorBlockValue).prod) = 595729980056158291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_283
      · exact prime_oneHundredThirtyFiveEC_58620243193
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 595729980056158291) ^ 297864990028079145 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 198576660018719430 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 119145996011231658 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 85104282865165470 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 31354209476639910 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 2105052933060630 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 595729980056158291) ^ 10162530 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_618877695587683109 : Nat.Prime 618877695587683109 := by
  apply lucas_primality 618877695587683109 (2 : ZMod 618877695587683109)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (109, 1), (367, 1), (19141, 1), (202063399, 1)] : List FactorBlock).map factorBlockValue).prod) = 618877695587683109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_109
      · exact prime_oneHundredThirtyFiveEC_367
      · exact prime_oneHundredThirtyFiveEC_19141
      · exact prime_oneHundredThirtyFiveEC_202063399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 618877695587683109) ^ 309438847793841554 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 5677777023740212 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 1686315246832924 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 32332568600788 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 618877695587683109) ^ 3062789692 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_632937469657326481 : Nat.Prime 632937469657326481 := by
  apply lucas_primality 632937469657326481 (13 : ZMod 632937469657326481)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (23, 1), (79, 1), (109, 1), (479, 1), (9266407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (23, 1), (79, 1), (109, 1), (479, 1), (9266407, 1)] : List FactorBlock).map factorBlockValue).prod) = 632937469657326481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_79
      · exact prime_oneHundredThirtyFiveEC_109
      · exact prime_oneHundredThirtyFiveEC_479
      · exact prime_oneHundredThirtyFiveEC_9266407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 632937469657326481) ^ 316468734828663240 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 210979156552442160 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 126587493931465296 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 27519020419883760 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 8011866704523120 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 5806765776672720 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 1321372588011120 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (13 : ZMod 632937469657326481) ^ 68304518640 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_919403975884809817 : Nat.Prime 919403975884809817 := by
  apply lucas_primality 919403975884809817 (10 : ZMod 919403975884809817)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (31, 1), (307, 1), (439799, 1), (1016947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (31, 1), (307, 1), (439799, 1), (1016947, 1)] : List FactorBlock).map factorBlockValue).prod) = 919403975884809817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_307
      · exact prime_oneHundredThirtyFiveEC_439799
      · exact prime_oneHundredThirtyFiveEC_1016947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 919403975884809817) ^ 459701987942404908 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 919403975884809817) ^ 306467991961603272 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 919403975884809817) ^ 29658192770477736 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 919403975884809817) ^ 2994801224380488 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 919403975884809817) ^ 2090509473384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 919403975884809817) ^ 904082489928 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_969057377255761897 : Nat.Prime 969057377255761897 := by
  apply lucas_primality 969057377255761897 (7 : ZMod 969057377255761897)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (40377390718990079, 1)] : List FactorBlock).map factorBlockValue).prod) = 969057377255761897 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_40377390718990079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 969057377255761897) ^ 484528688627880948 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 323019125751920632 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 969057377255761897) ^ 24 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1130281679714297003 : Nat.Prime 1130281679714297003 := by
  apply lucas_primality 1130281679714297003 (2 : ZMod 1130281679714297003)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (173, 1), (557, 1), (659, 1), (81647611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (173, 1), (557, 1), (659, 1), (81647611, 1)] : List FactorBlock).map factorBlockValue).prod) = 1130281679714297003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_109
      · exact prime_oneHundredThirtyFiveEC_173
      · exact prime_oneHundredThirtyFiveEC_557
      · exact prime_oneHundredThirtyFiveEC_659
      · exact prime_oneHundredThirtyFiveEC_81647611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1130281679714297003) ^ 565140839857148501 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130281679714297003) ^ 10369556694626578 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130281679714297003) ^ 6533420113955474 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130281679714297003) ^ 2029231022826386 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130281679714297003) ^ 1715146706698478 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1130281679714297003) ^ 13843413982 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1414732186084233811 : Nat.Prime 1414732186084233811 := by
  apply lucas_primality 1414732186084233811 (7 : ZMod 1414732186084233811)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (71, 1), (10733, 1), (61883305189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (71, 1), (10733, 1), (61883305189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1414732186084233811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_10733
      · exact prime_oneHundredThirtyFiveEC_61883305189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1414732186084233811) ^ 707366093042116905 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1414732186084233811) ^ 471577395361411270 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1414732186084233811) ^ 282946437216846762 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1414732186084233811) ^ 19925805437806110 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1414732186084233811) ^ 131811440052570 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 1414732186084233811) ^ 22861290 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1608309624659490097 : Nat.Prime 1608309624659490097 := by
  apply lucas_primality 1608309624659490097 (5 : ZMod 1608309624659490097)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (40487, 1), (160907, 1), (5143253, 1)] : List FactorBlock).map factorBlockValue).prod) = 1608309624659490097 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_40487
      · exact prime_oneHundredThirtyFiveEC_160907
      · exact prime_oneHundredThirtyFiveEC_5143253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1608309624659490097) ^ 804154812329745048 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 536103208219830032 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 39724099702608 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 9995274442128 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 1608309624659490097) ^ 312702802032 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3677615903539239269 : Nat.Prime 3677615903539239269 := by
  apply lucas_primality 3677615903539239269 (2 : ZMod 3677615903539239269)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (919403975884809817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (919403975884809817, 1)] : List FactorBlock).map factorBlockValue).prod) = 3677615903539239269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_919403975884809817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 3677615903539239269) ^ 1838807951769619634 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3677615903539239269) ^ 4 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4253332428539469313 : Nat.Prime 4253332428539469313 := by
  apply lucas_primality 4253332428539469313 (10 : ZMod 4253332428539469313)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3, 1), (59, 1), (46933841240063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3, 1), (59, 1), (46933841240063, 1)] : List FactorBlock).map factorBlockValue).prod) = 4253332428539469313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_59
      · exact prime_oneHundredThirtyFiveEC_46933841240063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 4253332428539469313) ^ 2126666214269734656 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 4253332428539469313) ^ 1417777476179823104 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 4253332428539469313) ^ 72090380144736768 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 4253332428539469313) ^ 90624 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4527184655447032079 : Nat.Prime 4527184655447032079 := by
  apply lucas_primality 4527184655447032079 (7 : ZMod 4527184655447032079)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4527184655447032079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_5821
      · exact prime_oneHundredThirtyFiveEC_152597
      · exact prime_oneHundredThirtyFiveEC_110796689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4527184655447032079) ^ 2263592327723516039 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 196834115454218786 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 777733148161318 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 29667586226774 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 40860288302 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7704145477076138227 : Nat.Prime 7704145477076138227 := by
  apply lucas_primality 7704145477076138227 (2 : ZMod 7704145477076138227)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (149, 1), (34608885102271, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (149, 1), (34608885102271, 1)] : List FactorBlock).map factorBlockValue).prod) = 7704145477076138227 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_83
      · exact prime_oneHundredThirtyFiveEC_149
      · exact prime_oneHundredThirtyFiveEC_34608885102271
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7704145477076138227) ^ 3852072738538069113 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7704145477076138227) ^ 2568048492358712742 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7704145477076138227) ^ 92821029844290822 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7704145477076138227) ^ 51705674342792874 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7704145477076138227) ^ 222606 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_35666719808417469181 : Nat.Prime 35666719808417469181 := by
  apply lucas_primality 35666719808417469181 (2 : ZMod 35666719808417469181)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (2801, 1), (23580678731417, 1)] : List FactorBlock).map factorBlockValue).prod) = 35666719808417469181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_2801
      · exact prime_oneHundredThirtyFiveEC_23580678731417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 35666719808417469181) ^ 17833359904208734590 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 11888906602805823060 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 7133343961683493836 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 12733566514965180 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 35666719808417469181) ^ 1512540 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_36265159998777480317 : Nat.Prime 36265159998777480317 := by
  apply lucas_primality 36265159998777480317 (5 : ZMod 36265159998777480317)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36265159998777480317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_29
      · exact prime_oneHundredThirtyFiveEC_73
      · exact prime_oneHundredThirtyFiveEC_47061672383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36265159998777480317) ^ 18132579999388740158 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 5180737142682497188 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 2789627692213652332 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 1250522758578533804 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 496783013681883292 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 770588 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_41715381632189132261 : Nat.Prime 41715381632189132261 := by
  apply lucas_primality 41715381632189132261 (2 : ZMod 41715381632189132261)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (41, 1), (129007363, 1), (394337311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (41, 1), (129007363, 1), (394337311, 1)] : List FactorBlock).map factorBlockValue).prod) = 41715381632189132261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_129007363
      · exact prime_oneHundredThirtyFiveEC_394337311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41715381632189132261) ^ 20857690816094566130 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 41715381632189132261) ^ 8343076326437826452 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 41715381632189132261) ^ 1017448332492417860 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 41715381632189132261) ^ 323356595020 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 41715381632189132261) ^ 105786037660 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_52533064873537140481 : Nat.Prime 52533064873537140481 := by
  apply lucas_primality 52533064873537140481 (11 : ZMod 52533064873537140481)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (7, 1), (1699, 1), (123731, 1), (9296759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (7, 1), (1699, 1), (123731, 1), (9296759, 1)] : List FactorBlock).map factorBlockValue).prod) = 52533064873537140481 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_1699
      · exact prime_oneHundredThirtyFiveEC_123731
      · exact prime_oneHundredThirtyFiveEC_9296759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 52533064873537140481) ^ 26266532436768570240 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 17511021624512380160 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 10506612974707428096 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 7504723553362448640 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 30919991096843520 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 424574802382080 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 52533064873537140481) ^ 5650685886720 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2063
      · exact prime_oneHundredThirtyFiveEC_15269
      · exact prime_oneHundredThirtyFiveEC_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_61397902960553752909 : Nat.Prime 61397902960553752909 := by
  apply lucas_primality 61397902960553752909 (6 : ZMod 61397902960553752909)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1097, 1), (666296641929871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1097, 1), (666296641929871, 1)] : List FactorBlock).map factorBlockValue).prod) = 61397902960553752909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_1097
      · exact prime_oneHundredThirtyFiveEC_666296641929871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 61397902960553752909) ^ 30698951480276876454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 61397902960553752909) ^ 20465967653517917636 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 61397902960553752909) ^ 8771128994364821844 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 61397902960553752909) ^ 55968917922109164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 61397902960553752909) ^ 92148 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_133428789850506403081 : Nat.Prime 133428789850506403081 := by
  apply lucas_primality 133428789850506403081 (7 : ZMod 133428789850506403081)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (42379, 1), (48571, 1), (540182551, 1)] : List FactorBlock).map factorBlockValue).prod) = 133428789850506403081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_42379
      · exact prime_oneHundredThirtyFiveEC_48571
      · exact prime_oneHundredThirtyFiveEC_540182551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 133428789850506403081) ^ 66714394925253201540 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 44476263283502134360 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 26685757970101280616 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 3148464802154520 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 2747087559459480 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 133428789850506403081) ^ 247006849080 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_141948996516209640817 : Nat.Prime 141948996516209640817 := by
  apply lucas_primality 141948996516209640817 (5 : ZMod 141948996516209640817)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (2011, 1), (7104093574121, 1)] : List FactorBlock).map factorBlockValue).prod) = 141948996516209640817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_2011
      · exact prime_oneHundredThirtyFiveEC_7104093574121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 141948996516209640817) ^ 70974498258104820408 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 47316332172069880272 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 6171695500704766992 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 70586273752466256 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 141948996516209640817) ^ 19981296 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_6863
      · exact prime_oneHundredThirtyFiveEC_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_277150409895147902543 : Nat.Prime 277150409895147902543 := by
  apply lucas_primality 277150409895147902543 (5 : ZMod 277150409895147902543)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (13, 1), (969057377255761897, 1)] : List FactorBlock).map factorBlockValue).prod) = 277150409895147902543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_969057377255761897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 277150409895147902543) ^ 138575204947573951271 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 25195491808649809322 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 21319262299626761734 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 277150409895147902543) ^ 286 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_288443951781534738289 : Nat.Prime 288443951781534738289 := by
  apply lucas_primality 288443951781534738289 (38 : ZMod 288443951781534738289)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (11, 1), (109, 1), (185625335787497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (11, 1), (109, 1), (185625335787497, 1)] : List FactorBlock).map factorBlockValue).prod) = 288443951781534738289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_109
      · exact prime_oneHundredThirtyFiveEC_185625335787497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (38 : ZMod 288443951781534738289) ^ 144221975890767369144 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (38 : ZMod 288443951781534738289) ^ 96147983927178246096 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (38 : ZMod 288443951781534738289) ^ 26222177434684976208 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (38 : ZMod 288443951781534738289) ^ 2646274786986557232 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (38 : ZMod 288443951781534738289) ^ 1553904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_348773259140236483667 : Nat.Prime 348773259140236483667 := by
  apply lucas_primality 348773259140236483667 (2 : ZMod 348773259140236483667)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (4253332428539469313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (4253332428539469313, 1)] : List FactorBlock).map factorBlockValue).prod) = 348773259140236483667 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_4253332428539469313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 348773259140236483667) ^ 174386629570118241833 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 348773259140236483667) ^ 8506664857078938626 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 348773259140236483667) ^ 82 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_396864253671680020903 : Nat.Prime 396864253671680020903 := by
  apply lucas_primality 396864253671680020903 (5 : ZMod 396864253671680020903)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (659, 1), (394577, 1), (19567268263, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (659, 1), (394577, 1), (19567268263, 1)] : List FactorBlock).map factorBlockValue).prod) = 396864253671680020903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_659
      · exact prime_oneHundredThirtyFiveEC_394577
      · exact prime_oneHundredThirtyFiveEC_19567268263
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 396864253671680020903) ^ 198432126835840010451 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 396864253671680020903) ^ 132288084557226673634 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 396864253671680020903) ^ 30528019513206155454 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 396864253671680020903) ^ 602221932733960578 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 396864253671680020903) ^ 1005796723254726 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 396864253671680020903) ^ 20282046954 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_829821849978416232493 : Nat.Prime 829821849978416232493 := by
  apply lucas_primality 829821849978416232493 (5 : ZMod 829821849978416232493)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) = 829821849978416232493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_127
      · exact prime_oneHundredThirtyFiveEC_947
      · exact prime_oneHundredThirtyFiveEC_11437
      · exact prime_oneHundredThirtyFiveEC_1861975811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829821849978416232493) ^ 414910924989208116246 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 276607283326138744164 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 6534030314790678996 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 876263833134547236 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 72555901895463516 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 445667363172 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_900048136962172065887 : Nat.Prime 900048136962172065887 := by
  apply lucas_primality 900048136962172065887 (5 : ZMod 900048136962172065887)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (131, 1), (14717, 1), (1099249, 1), (212348441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (131, 1), (14717, 1), (1099249, 1), (212348441, 1)] : List FactorBlock).map factorBlockValue).prod) = 900048136962172065887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_131
      · exact prime_oneHundredThirtyFiveEC_14717
      · exact prime_oneHundredThirtyFiveEC_1099249
      · exact prime_oneHundredThirtyFiveEC_212348441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 900048136962172065887) ^ 450024068481086032943 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 900048136962172065887) ^ 6870596465360092106 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 900048136962172065887) ^ 61157038592251958 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 900048136962172065887) ^ 818784585623614 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 900048136962172065887) ^ 4238543653646 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1047198039805151282999 : Nat.Prime 1047198039805151282999 := by
  apply lucas_primality 1047198039805151282999 (11 : ZMod 1047198039805151282999)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (997, 1), (11909, 1), (1379513, 1), (31967051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (997, 1), (11909, 1), (1379513, 1), (31967051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1047198039805151282999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_997
      · exact prime_oneHundredThirtyFiveEC_11909
      · exact prime_oneHundredThirtyFiveEC_1379513
      · exact prime_oneHundredThirtyFiveEC_31967051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1047198039805151282999) ^ 523599019902575641499 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1047198039805151282999) ^ 1050349087066350334 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1047198039805151282999) ^ 87933331077769022 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1047198039805151282999) ^ 759107047055846 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 1047198039805151282999) ^ 32758668912098 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_199
      · exact prime_oneHundredThirtyFiveEC_52864081
      · exact prime_oneHundredThirtyFiveEC_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_23
      · exact prime_oneHundredThirtyFiveEC_1549
      · exact prime_oneHundredThirtyFiveEC_47713
      · exact prime_oneHundredThirtyFiveEC_341461
      · exact prime_oneHundredThirtyFiveEC_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3019418713742564280571 : Nat.Prime 3019418713742564280571 := by
  apply lucas_primality 3019418713742564280571 (10 : ZMod 3019418713742564280571)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019418713742564280571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_97
      · exact prime_oneHundredThirtyFiveEC_4671071
      · exact prime_oneHundredThirtyFiveEC_222133410637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019418713742564280571) ^ 1509709356871282140285 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 1006472904580854760190 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 603883742748512856114 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 31128027976727466810 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 646408224953670 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 13592816610 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_4035506599621491560801 : Nat.Prime 4035506599621491560801 := by
  apply lucas_primality 4035506599621491560801 (3 : ZMod 4035506599621491560801)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 2), (13, 1), (179, 1), (5119, 1), (423473815627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 2), (13, 1), (179, 1), (5119, 1), (423473815627, 1)] : List FactorBlock).map factorBlockValue).prod) = 4035506599621491560801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_179
      · exact prime_oneHundredThirtyFiveEC_5119
      · exact prime_oneHundredThirtyFiveEC_423473815627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4035506599621491560801) ^ 2017753299810745780400 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4035506599621491560801) ^ 807101319924298312160 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4035506599621491560801) ^ 310423584586268581600 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4035506599621491560801) ^ 22544729606823975200 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4035506599621491560801) ^ 788338855171223200 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 4035506599621491560801) ^ 9529530400 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_8357372316971481634087 : Nat.Prime 8357372316971481634087 := by
  apply lucas_primality 8357372316971481634087 (5 : ZMod 8357372316971481634087)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (47, 1), (12139741, 1), (2540316523, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (47, 1), (12139741, 1), (2540316523, 1)] : List FactorBlock).map factorBlockValue).prod) = 8357372316971481634087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_12139741
      · exact prime_oneHundredThirtyFiveEC_2540316523
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8357372316971481634087) ^ 4178686158485740817043 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8357372316971481634087) ^ 2785790772323827211362 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8357372316971481634087) ^ 269592655386176826906 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8357372316971481634087) ^ 177816432275988970938 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8357372316971481634087) ^ 688430858366046 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8357372316971481634087) ^ 3289894090482 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_8993759679696815118617 : Nat.Prime 8993759679696815118617 := by
  apply lucas_primality 8993759679696815118617 (3 : ZMod 8993759679696815118617)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993759679696815118617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_31
      · exact prime_oneHundredThirtyFiveEC_36265159998777480317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8993759679696815118617) ^ 4496879839848407559308 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 290121279990219842536 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 248 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_17064909035376275873347 : Nat.Prime 17064909035376275873347 := by
  apply lucas_primality 17064909035376275873347 (2 : ZMod 17064909035376275873347)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (4793, 1), (92512139, 1), (6414260233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (4793, 1), (92512139, 1), (6414260233, 1)] : List FactorBlock).map factorBlockValue).prod) = 17064909035376275873347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_4793
      · exact prime_oneHundredThirtyFiveEC_92512139
      · exact prime_oneHundredThirtyFiveEC_6414260233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17064909035376275873347) ^ 8532454517688137936673 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 17064909035376275873347) ^ 5688303011792091957782 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 17064909035376275873347) ^ 3560381605544810322 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 17064909035376275873347) ^ 184461295780614 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 17064909035376275873347) ^ 2660464093362 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_21123484649574631668391 : Nat.Prime 21123484649574631668391 := by
  apply lucas_primality 21123484649574631668391 (3 : ZMod 21123484649574631668391)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (555817231, 1), (1266812390323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (555817231, 1), (1266812390323, 1)] : List FactorBlock).map factorBlockValue).prod) = 21123484649574631668391 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_555817231
      · exact prime_oneHundredThirtyFiveEC_1266812390323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 21123484649574631668391) ^ 10561742324787315834195 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 21123484649574631668391) ^ 7041161549858210556130 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 21123484649574631668391) ^ 4224696929914926333678 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 21123484649574631668391) ^ 38004371709690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 21123484649574631668391) ^ 16674516930 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_102429416767293794920459 : Nat.Prime 102429416767293794920459 := by
  apply lucas_primality 102429416767293794920459 (3 : ZMod 102429416767293794920459)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2063, 1), (2115948589, 1), (3910831549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2063, 1), (2115948589, 1), (3910831549, 1)] : List FactorBlock).map factorBlockValue).prod) = 102429416767293794920459 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2063
      · exact prime_oneHundredThirtyFiveEC_2115948589
      · exact prime_oneHundredThirtyFiveEC_3910831549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 102429416767293794920459) ^ 51214708383646897460229 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 34143138922431264973486 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 49650710987539406166 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 48408272913522 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 102429416767293794920459) ^ 26191211634642 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_119432335722299649883441 : Nat.Prime 119432335722299649883441 := by
  apply lucas_primality 119432335722299649883441 (14 : ZMod 119432335722299649883441)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (5, 1), (75363469, 1), (2201043108283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (5, 1), (75363469, 1), (2201043108283, 1)] : List FactorBlock).map factorBlockValue).prod) = 119432335722299649883441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_75363469
      · exact prime_oneHundredThirtyFiveEC_2201043108283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 119432335722299649883441) ^ 59716167861149824941720 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 119432335722299649883441) ^ 39810778574099883294480 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 119432335722299649883441) ^ 23886467144459929976688 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 119432335722299649883441) ^ 1584751037963760 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 119432335722299649883441) ^ 54261697680 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_122499940021721448817171 : Nat.Prime 122499940021721448817171 := by
  apply lucas_primality 122499940021721448817171 (2 : ZMod 122499940021721448817171)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (53, 1), (67, 1), (281, 1), (59598493, 1), (68662933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (53, 1), (67, 1), (281, 1), (59598493, 1), (68662933, 1)] : List FactorBlock).map factorBlockValue).prod) = 122499940021721448817171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_53
      · exact prime_oneHundredThirtyFiveEC_67
      · exact prime_oneHundredThirtyFiveEC_281
      · exact prime_oneHundredThirtyFiveEC_59598493
      · exact prime_oneHundredThirtyFiveEC_68662933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 122499940021721448817171) ^ 61249970010860724408585 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 40833313340573816272390 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 24499988004344289763434 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 2311319623051348090890 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 1828357313757036549510 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 435942847052389497570 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 2055420092949690 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 122499940021721448817171) ^ 1784076716060490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_132396991279118172886049 : Nat.Prime 132396991279118172886049 := by
  apply lucas_primality 132396991279118172886049 (6 : ZMod 132396991279118172886049)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (11, 1), (17, 1), (311517887, 1), (10146248683, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (11, 1), (17, 1), (311517887, 1), (10146248683, 1)] : List FactorBlock).map factorBlockValue).prod) = 132396991279118172886049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_11
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_311517887
      · exact prime_oneHundredThirtyFiveEC_10146248683
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 132396991279118172886049) ^ 66198495639559086443024 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 132396991279118172886049) ^ 18913855897016881840864 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 132396991279118172886049) ^ 12036090116283470262368 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 132396991279118172886049) ^ 7788058310536363110944 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 132396991279118172886049) ^ 425006064833504 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 132396991279118172886049) ^ 13048861250656 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_259193266026634557332219 : Nat.Prime 259193266026634557332219 := by
  apply lucas_primality 259193266026634557332219 (2 : ZMod 259193266026634557332219)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) = 259193266026634557332219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_71
      · exact prime_oneHundredThirtyFiveEC_19471
      · exact prime_oneHundredThirtyFiveEC_273308408322643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259193266026634557332219) ^ 129596633013317278666109 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 37027609432376365333174 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 3650609380656824751158 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 13311759335762649958 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 948354526 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1561611151535927711817641 : Nat.Prime 1561611151535927711817641 := by
  apply lucas_primality 1561611151535927711817641 (3 : ZMod 1561611151535927711817641)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (7, 1), (83780407, 1), (66569056940209, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (7, 1), (83780407, 1), (66569056940209, 1)] : List FactorBlock).map factorBlockValue).prod) = 1561611151535927711817641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_83780407
      · exact prime_oneHundredThirtyFiveEC_66569056940209
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1561611151535927711817641) ^ 780805575767963855908820 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561611151535927711817641) ^ 312322230307185542363528 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561611151535927711817641) ^ 223087307362275387402520 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561611151535927711817641) ^ 18639335943258520 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1561611151535927711817641) ^ 23458513960 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_3288201844988175028616861 : Nat.Prime 3288201844988175028616861 := by
  apply lucas_primality 3288201844988175028616861 (3 : ZMod 3288201844988175028616861)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (157, 1), (1047198039805151282999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (157, 1), (1047198039805151282999, 1)] : List FactorBlock).map factorBlockValue).prod) = 3288201844988175028616861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_157
      · exact prime_oneHundredThirtyFiveEC_1047198039805151282999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 3288201844988175028616861) ^ 1644100922494087514308430 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3288201844988175028616861) ^ 657640368997635005723372 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3288201844988175028616861) ^ 20943960796103025659980 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 3288201844988175028616861) ^ 3140 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7844975637939593399559293 : Nat.Prime 7844975637939593399559293 := by
  apply lucas_primality 7844975637939593399559293 (2 : ZMod 7844975637939593399559293)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (617, 1), (13267, 1), (41257, 1), (829617739043, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (617, 1), (13267, 1), (41257, 1), (829617739043, 1)] : List FactorBlock).map factorBlockValue).prod) = 7844975637939593399559293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_617
      · exact prime_oneHundredThirtyFiveEC_13267
      · exact prime_oneHundredThirtyFiveEC_41257
      · exact prime_oneHundredThirtyFiveEC_829617739043
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7844975637939593399559293) ^ 3922487818969796699779646 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 1120710805419941914222756 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 12714709299740021717276 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 591314964795326253076 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 190148959884131017756 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 7844975637939593399559293) ^ 9456132949844 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_8953050392880519869525653 : Nat.Prime 8953050392880519869525653 := by
  apply lucas_primality 8953050392880519869525653 (5 : ZMod 8953050392880519869525653)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (61, 1), (24701077187, 1), (70736898679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (61, 1), (24701077187, 1), (70736898679, 1)] : List FactorBlock).map factorBlockValue).prod) = 8953050392880519869525653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_61
      · exact prime_oneHundredThirtyFiveEC_24701077187
      · exact prime_oneHundredThirtyFiveEC_70736898679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 8953050392880519869525653) ^ 4476525196440259934762826 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8953050392880519869525653) ^ 2984350130960173289841884 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8953050392880519869525653) ^ 1279007198982931409932236 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8953050392880519869525653) ^ 146771317916074096221732 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8953050392880519869525653) ^ 362455868831196 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 8953050392880519869525653) ^ 126568319506188 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_11246989595791771384260011 : Nat.Prime 11246989595791771384260011 := by
  apply lucas_primality 11246989595791771384260011 (2 : ZMod 11246989595791771384260011)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5749, 1), (9341, 1), (20943565178693489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5749, 1), (9341, 1), (20943565178693489, 1)] : List FactorBlock).map factorBlockValue).prod) = 11246989595791771384260011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_5749
      · exact prime_oneHundredThirtyFiveEC_9341
      · exact prime_oneHundredThirtyFiveEC_20943565178693489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11246989595791771384260011) ^ 5623494797895885692130005 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246989595791771384260011) ^ 2249397919158354276852002 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246989595791771384260011) ^ 1956338423341758807490 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246989595791771384260011) ^ 1204045562123088682610 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11246989595791771384260011) ^ 537014090 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_35279847337285815144569809 : Nat.Prime 35279847337285815144569809 := by
  apply lucas_primality 35279847337285815144569809 (11 : ZMod 35279847337285815144569809)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (83186137633, 1), (1262224075241, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (83186137633, 1), (1262224075241, 1)] : List FactorBlock).map factorBlockValue).prod) = 35279847337285815144569809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_83186137633
      · exact prime_oneHundredThirtyFiveEC_1262224075241
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 35279847337285815144569809) ^ 17639923668642907572284904 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 35279847337285815144569809) ^ 11759949112428605048189936 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 35279847337285815144569809) ^ 5039978191040830734938544 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 35279847337285815144569809) ^ 424107289280976 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (11 : ZMod 35279847337285815144569809) ^ 27950542244688 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_36159046070204129522889401 : Nat.Prime 36159046070204129522889401 := by
  apply lucas_primality 36159046070204129522889401 (6 : ZMod 36159046070204129522889401)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (13, 1), (449, 1), (222791, 1), (552137, 1), (251798293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (13, 1), (449, 1), (222791, 1), (552137, 1), (251798293, 1)] : List FactorBlock).map factorBlockValue).prod) = 36159046070204129522889401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_449
      · exact prime_oneHundredThirtyFiveEC_222791
      · exact prime_oneHundredThirtyFiveEC_552137
      · exact prime_oneHundredThirtyFiveEC_251798293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 36159046070204129522889401) ^ 18079523035102064761444700 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 7231809214040825904577880 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 2781465082323394578683800 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 80532396592882248380600 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 162300299698839403400 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 65489264566953726200 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 36159046070204129522889401) ^ 143603221608035800 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_68062272645578263417498429 : Nat.Prime 68062272645578263417498429 := by
  apply lucas_primality 68062272645578263417498429 (2 : ZMod 68062272645578263417498429)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (19, 1), (701, 1), (141948996516209640817, 1)] : List FactorBlock).map factorBlockValue).prod) = 68062272645578263417498429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_701
      · exact prime_oneHundredThirtyFiveEC_141948996516209640817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 68062272645578263417498429) ^ 34031136322789131708749214 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 22687424215192754472499476 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 3582224876083066495657812 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 97093113617087394318828 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 68062272645578263417498429) ^ 479484 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_360284490640814960979760307 : Nat.Prime 360284490640814960979760307 := by
  apply lucas_primality 360284490640814960979760307 (2 : ZMod 360284490640814960979760307)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1201, 1), (17597, 1), (687923, 1), (12390650303663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1201, 1), (17597, 1), (687923, 1), (12390650303663, 1)] : List FactorBlock).map factorBlockValue).prod) = 360284490640814960979760307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_1201
      · exact prime_oneHundredThirtyFiveEC_17597
      · exact prime_oneHundredThirtyFiveEC_687923
      · exact prime_oneHundredThirtyFiveEC_12390650303663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 360284490640814960979760307) ^ 180142245320407480489880153 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 360284490640814960979760307) ^ 299987086295432940033106 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 360284490640814960979760307) ^ 20474199615889922201498 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 360284490640814960979760307) ^ 523727932691325862022 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 360284490640814960979760307) ^ 29077125236462 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_548474327676567105546507959 : Nat.Prime 548474327676567105546507959 := by
  apply lucas_primality 548474327676567105546507959 (7 : ZMod 548474327676567105546507959)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (151, 1), (172669379, 1), (10518021020214751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (151, 1), (172669379, 1), (10518021020214751, 1)] : List FactorBlock).map factorBlockValue).prod) = 548474327676567105546507959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_151
      · exact prime_oneHundredThirtyFiveEC_172669379
      · exact prime_oneHundredThirtyFiveEC_10518021020214751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 548474327676567105546507959) ^ 274237163838283552773253979 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 548474327676567105546507959) ^ 3632280315738855003619258 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 548474327676567105546507959) ^ 3176442348104854802 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 548474327676567105546507959) ^ 52146152458 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_613869343668773183515514677 : Nat.Prime 613869343668773183515514677 := by
  apply lucas_primality 613869343668773183515514677 (6 : ZMod 613869343668773183515514677)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (17, 1), (47, 1), (14779, 1), (618877695587683109, 1)] : List FactorBlock).map factorBlockValue).prod) = 613869343668773183515514677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_14779
      · exact prime_oneHundredThirtyFiveEC_618877695587683109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 613869343668773183515514677) ^ 306934671834386591757757338 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 204623114556257727838504892 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 87695620524110454787930668 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 36109961392280775500912628 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 13061049865293046457776908 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 41536595417062939543644 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 613869343668773183515514677) ^ 991907364 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_635880595035382580533999267 : Nat.Prime 635880595035382580533999267 := by
  apply lucas_primality 635880595035382580533999267 (5 : ZMod 635880595035382580533999267)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (83, 1), (773, 1), (9613, 1), (57277827640317811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (83, 1), (773, 1), (9613, 1), (57277827640317811, 1)] : List FactorBlock).map factorBlockValue).prod) = 635880595035382580533999267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_83
      · exact prime_oneHundredThirtyFiveEC_773
      · exact prime_oneHundredThirtyFiveEC_9613
      · exact prime_oneHundredThirtyFiveEC_57277827640317811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 635880595035382580533999267) ^ 317940297517691290266999633 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 635880595035382580533999267) ^ 211960198345127526844666422 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 635880595035382580533999267) ^ 7661211988378103379927702 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 635880595035382580533999267) ^ 822613965116924425011642 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 635880595035382580533999267) ^ 66147986584352707847082 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (5 : ZMod 635880595035382580533999267) ^ 11101688406 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_806091057342833473303201091 : Nat.Prime 806091057342833473303201091 := by
  apply lucas_primality 806091057342833473303201091 (2 : ZMod 806091057342833473303201091)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) = 806091057342833473303201091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_311
      · exact prime_oneHundredThirtyFiveEC_259193266026634557332219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 806091057342833473303201091) ^ 403045528671416736651600545 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 161218211468566694660640218 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 2591932660266345573322190 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 3110 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1016598913082044762509769529 : Nat.Prime 1016598913082044762509769529 := by
  apply lucas_primality 1016598913082044762509769529 (3 : ZMod 1016598913082044762509769529)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (2082470272537, 1), (3589483176079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (2082470272537, 1), (3589483176079, 1)] : List FactorBlock).map factorBlockValue).prod) = 1016598913082044762509769529 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_17
      · exact prime_oneHundredThirtyFiveEC_2082470272537
      · exact prime_oneHundredThirtyFiveEC_3589483176079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1016598913082044762509769529) ^ 508299456541022381254884764 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1016598913082044762509769529) ^ 59799936063649691912339384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1016598913082044762509769529) ^ 488169711946744 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 1016598913082044762509769529) ^ 283215957065032 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_1834552061538862387517630069 : Nat.Prime 1834552061538862387517630069 := by
  apply lucas_primality 1834552061538862387517630069 (2 : ZMod 1834552061538862387517630069)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (35279847337285815144569809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (35279847337285815144569809, 1)] : List FactorBlock).map factorBlockValue).prod) = 1834552061538862387517630069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_35279847337285815144569809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1834552061538862387517630069) ^ 917276030769431193758815034 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834552061538862387517630069) ^ 141119389349143260578279236 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 1834552061538862387517630069) ^ 52 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_2616492284489852913344816657 : Nat.Prime 2616492284489852913344816657 := by
  apply lucas_primality 2616492284489852913344816657 (3 : ZMod 2616492284489852913344816657)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (19, 1), (2309, 1), (5037091, 1), (740017763996981, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (19, 1), (2309, 1), (5037091, 1), (740017763996981, 1)] : List FactorBlock).map factorBlockValue).prod) = 2616492284489852913344816657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_2309
      · exact prime_oneHundredThirtyFiveEC_5037091
      · exact prime_oneHundredThirtyFiveEC_740017763996981
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2616492284489852913344816657) ^ 1308246142244926456672408328 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2616492284489852913344816657) ^ 137710120236308048070779824 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2616492284489852913344816657) ^ 1133171192936272374770384 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2616492284489852913344816657) ^ 519445109188984855216 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 2616492284489852913344816657) ^ 3535715508176 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_6384241174155241108561352641 : Nat.Prime 6384241174155241108561352641 := by
  apply lucas_primality 6384241174155241108561352641 (7 : ZMod 6384241174155241108561352641)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (5, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 6384241174155241108561352641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_171401
      · exact prime_oneHundredThirtyFiveEC_714027719
      · exact prime_oneHundredThirtyFiveEC_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6384241174155241108561352641) ^ 3192120587077620554280676320 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 2128080391385080369520450880 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1276848234831048221712270528 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 37247397472332373256640 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 8941167134374570560 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (7 : ZMod 6384241174155241108561352641) ^ 1057406962155716160 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_7254819516085501259728809821 : Nat.Prime 7254819516085501259728809821 := by
  apply lucas_primality 7254819516085501259728809821 (14 : ZMod 7254819516085501259728809821)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) = 7254819516085501259728809821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_388373
      · exact prime_oneHundredThirtyFiveEC_133428789850506403081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 7254819516085501259728809821) ^ 3627409758042750629864404910 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 7254819516085501259728809821) ^ 1450963903217100251945761964 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 7254819516085501259728809821) ^ 1036402788012214465675544260 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 7254819516085501259728809821) ^ 18680030579070896431340 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (14 : ZMod 7254819516085501259728809821) ^ 54372220 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_11400430668134359122430986859 : Nat.Prime 11400430668134359122430986859 := by
  apply lucas_primality 11400430668134359122430986859 (2 : ZMod 11400430668134359122430986859)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11976257000707, 1), (158653223449549, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11976257000707, 1), (158653223449549, 1)] : List FactorBlock).map factorBlockValue).prod) = 11400430668134359122430986859 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_11976257000707
      · exact prime_oneHundredThirtyFiveEC_158653223449549
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11400430668134359122430986859) ^ 5700215334067179561215493429 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11400430668134359122430986859) ^ 3800143556044786374143662286 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11400430668134359122430986859) ^ 951919340697294 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 11400430668134359122430986859) ^ 71857542004242 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_15960602935388102771403381607 : Nat.Prime 15960602935388102771403381607 := by
  apply lucas_primality 15960602935388102771403381607 (3 : ZMod 15960602935388102771403381607)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 15960602935388102771403381607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_2411
      · exact prime_oneHundredThirtyFiveEC_7039
      · exact prime_oneHundredThirtyFiveEC_188911
      · exact prime_oneHundredThirtyFiveEC_829722028640579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15960602935388102771403381607) ^ 7980301467694051385701690803 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 5320200978462700923801127202 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 6619909969053547395853746 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 2267453180194360388038554 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 84487419659988580714746 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 15960602935388102771403381607) ^ 19236084356514 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_19950753669235128464254227007 : Nat.Prime 19950753669235128464254227007 := by
  apply lucas_primality 19950753669235128464254227007 (3 : ZMod 19950753669235128464254227007)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (190986192499, 1), (17410293215602999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (190986192499, 1), (17410293215602999, 1)] : List FactorBlock).map factorBlockValue).prod) = 19950753669235128464254227007 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_190986192499
      · exact prime_oneHundredThirtyFiveEC_17410293215602999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 19950753669235128464254227007) ^ 9975376834617564232127113503 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19950753669235128464254227007) ^ 6650251223078376154751409002 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19950753669235128464254227007) ^ 104461759293617994 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 19950753669235128464254227007) ^ 1145917154994 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_53202009784627009238011272019 : Nat.Prime 53202009784627009238011272019 := by
  apply lucas_primality 53202009784627009238011272019 (3 : ZMod 53202009784627009238011272019)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 53202009784627009238011272019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_7
      · exact prime_oneHundredThirtyFiveEC_19
      · exact prime_oneHundredThirtyFiveEC_41
      · exact prime_oneHundredThirtyFiveEC_397
      · exact prime_oneHundredThirtyFiveEC_13617913
      · exact prime_oneHundredThirtyFiveEC_100257985466497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53202009784627009238011272019) ^ 26601004892313504619005636009 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 17734003261542336412670424006 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 7600287112089572748287324574 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 2800105778138263644105856422 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 1297609994747000225317348098 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 134010100213166270120935194 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 3906766755274982975586 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (3 : ZMod 53202009784627009238011272019) ^ 530651095142994 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_79803014676940513857016908011 : Nat.Prime 79803014676940513857016908011 := by
  apply lucas_primality 79803014676940513857016908011 (6 : ZMod 79803014676940513857016908011)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 79803014676940513857016908011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_5
      · exact prime_oneHundredThirtyFiveEC_13
      · exact prime_oneHundredThirtyFiveEC_613869343668773183515514677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 79803014676940513857016908011) ^ 39901507338470256928508454005 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79803014676940513857016908011) ^ 15960602935388102771403381602 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79803014676940513857016908011) ^ 6138693436687731835155146770 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (6 : ZMod 79803014676940513857016908011) ^ 130 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem prime_oneHundredThirtyFiveEC_159606029353881027714033816043 : Nat.Prime 159606029353881027714033816043 := by
  apply lucas_primality 159606029353881027714033816043 (2 : ZMod 159606029353881027714033816043)
  · rw [← oneHundredThirtyFiveECFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (47, 1), (1426127, 1), (396864253671680020903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (47, 1), (1426127, 1), (396864253671680020903, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816043 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredThirtyFiveEC_2
      · exact prime_oneHundredThirtyFiveEC_3
      · exact prime_oneHundredThirtyFiveEC_47
      · exact prime_oneHundredThirtyFiveEC_1426127
      · exact prime_oneHundredThirtyFiveEC_396864253671680020903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 159606029353881027714033816043) ^ 79803014676940513857016908021 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159606029353881027714033816043) ^ 53202009784627009238011272014 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159606029353881027714033816043) ^ 3395872964976192079021996086 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159606029353881027714033816043) ^ 111915719535413765894646 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide
    · change (2 : ZMod 159606029353881027714033816043) ^ 402167814 ≠ 1
      rw [← oneHundredThirtyFiveECFastPow_eq_pow]
      decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816000 : Nat.totient 159606029353881027714033816000 = 42561359445061686770242560000 := by
  rw [← show ((([(2, 6), (3, 3), (5, 3), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_171401, prime_oneHundredThirtyFiveEC_714027719, prime_oneHundredThirtyFiveEC_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816001 : Nat.totient 159606029353881027714033816001 = 159245744863240212753054055252 := by
  rw [← show ((([(443, 1), (360284490640814960979760307, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_443, prime_oneHundredThirtyFiveEC_360284490640814960979760307]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816002 : Nat.totient 159606029353881027714033816002 = 79765932136320357297784071840 := by
  rw [← show ((([(2, 1), (2153, 1), (4811171, 1), (7704145477076138227, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_2153, prime_oneHundredThirtyFiveEC_4811171, prime_oneHundredThirtyFiveEC_7704145477076138227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816003 : Nat.totient 159606029353881027714033816003 = 102734915446176293700987283808 := by
  rw [← show ((([(3, 1), (29, 1), (1834552061538862387517630069, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_29, prime_oneHundredThirtyFiveEC_1834552061538862387517630069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816004 : Nat.totient 159606029353881027714033816004 = 79411583985987230916107218560 := by
  rw [← show ((([(2, 2), (227, 1), (1997, 1), (880861, 1), (99925883771346739, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_227, prime_oneHundredThirtyFiveEC_1997, prime_oneHundredThirtyFiveEC_880861, prime_oneHundredThirtyFiveEC_99925883771346739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816005 : Nat.totient 159606029353881027714033816005 = 107810639870595969253317509952 := by
  rw [← show ((([(5, 1), (7, 1), (67, 1), (68062272645578263417498429, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_67, prime_oneHundredThirtyFiveEC_68062272645578263417498429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816006 : Nat.totient 159606029353881027714033816006 = 53202009782366445831512986664 := by
  rw [← show ((([(2, 1), (3, 1), (23534845667, 1), (1130281679714297003, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_23534845667, prime_oneHundredThirtyFiveEC_1130281679714297003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816007 : Nat.totient 159606029353881027714033816007 = 133935129527721165951385737600 := by
  rw [← show ((([(11, 1), (13, 1), (14147054523061, 1), (78894590925509, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_14147054523061, prime_oneHundredThirtyFiveEC_78894590925509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816008 : Nat.totient 159606029353881027714033816008 = 77091812742970861369178443776 := by
  rw [← show ((([(2, 3), (37, 1), (179, 1), (643, 1), (152753, 1), (30669297629253853, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_37, prime_oneHundredThirtyFiveEC_179, prime_oneHundredThirtyFiveEC_643, prime_oneHundredThirtyFiveEC_152753, prime_oneHundredThirtyFiveEC_30669297629253853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816009 : Nat.totient 159606029353881027714033816009 = 101034773234870314291407403008 := by
  rw [← show ((([(3, 2), (23, 1), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_23, prime_oneHundredThirtyFiveEC_137, prime_oneHundredThirtyFiveEC_1243169, prime_oneHundredThirtyFiveEC_4527184655447032079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816010 : Nat.totient 159606029353881027714033816010 = 63140848857911274824701209600 := by
  rw [← show ((([(2, 1), (5, 1), (173, 1), (191, 1), (300331, 1), (1608309624659490097, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_173, prime_oneHundredThirtyFiveEC_191, prime_oneHundredThirtyFiveEC_300331, prime_oneHundredThirtyFiveEC_1608309624659490097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816011 : Nat.totient 159606029353881027714033816011 = 159342518664454858279516569600 := by
  rw [← show ((([(881, 1), (2011, 1), (61153, 1), (343433, 1), (4289449148729, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_881, prime_oneHundredThirtyFiveEC_2011, prime_oneHundredThirtyFiveEC_61153, prime_oneHundredThirtyFiveEC_343433, prime_oneHundredThirtyFiveEC_4289449148729]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816012 : Nat.totient 159606029353881027714033816012 = 45601722672533341382193141312 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (11976257000707, 1), (158653223449549, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_11976257000707, prime_oneHundredThirtyFiveEC_158653223449549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816013 : Nat.totient 159606029353881027714033816013 = 154567120078824156350418729600 := by
  rw [← show ((([(41, 1), (149, 1), (1531, 1), (17064909035376275873347, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_41, prime_oneHundredThirtyFiveEC_149, prime_oneHundredThirtyFiveEC_1531, prime_oneHundredThirtyFiveEC_17064909035376275873347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816014 : Nat.totient 159606029353881027714033816014 = 79766855630870309727494016400 := by
  rw [← show ((([(2, 1), (2207, 1), (36159046070204129522889401, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_2207, prime_oneHundredThirtyFiveEC_36159046070204129522889401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816015 : Nat.totient 159606029353881027714033816015 = 78066458596338135682052063232 := by
  rw [← show ((([(3, 1), (5, 1), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_73, prime_oneHundredThirtyFiveEC_83, prime_oneHundredThirtyFiveEC_906208483, prime_oneHundredThirtyFiveEC_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816016 : Nat.totient 159606029353881027714033816016 = 74331244252708180618454784000 := by
  rw [← show ((([(2, 4), (19, 1), (61, 1), (2309, 1), (5037091, 1), (740017763996981, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_19, prime_oneHundredThirtyFiveEC_61, prime_oneHundredThirtyFiveEC_2309, prime_oneHundredThirtyFiveEC_5037091, prime_oneHundredThirtyFiveEC_740017763996981]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816017 : Nat.totient 159606029353881027714033816017 = 158970148758845645133499816500 := by
  rw [← show ((([(251, 1), (635880595035382580533999267, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_251, prime_oneHundredThirtyFiveEC_635880595035382580533999267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816018 : Nat.totient 159606029353881027714033816018 = 48365463440570008398192065400 := by
  rw [← show ((([(2, 1), (3, 2), (11, 1), (806091057342833473303201091, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_806091057342833473303201091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816019 : Nat.totient 159606029353881027714033816019 = 132392098081531287257151474000 := by
  rw [← show ((([(7, 2), (31, 1), (6271489433791, 1), (16754089251811, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_31, prime_oneHundredThirtyFiveEC_6271489433791, prime_oneHundredThirtyFiveEC_16754089251811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816020 : Nat.totient 159606029353881027714033816020 = 58931456992202225617489408896 := by
  rw [← show ((([(2, 2), (5, 1), (13, 1), (613869343668773183515514677, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_613869343668773183515514677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816021 : Nat.totient 159606029353881027714033816021 = 106332459198180886699153638000 := by
  rw [← show ((([(3, 1), (1487, 1), (25289651, 1), (1414732186084233811, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_1487, prime_oneHundredThirtyFiveEC_25289651, prime_oneHundredThirtyFiveEC_1414732186084233811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816022 : Nat.totient 159606029353881027714033816022 = 79803014676940513857016908010 := by
  rw [← show ((([(2, 1), (79803014676940513857016908011, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_79803014676940513857016908011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816023 : Nat.totient 159606029353881027714033816023 = 159579920073450841620777980928 := by
  rw [← show ((([(6113, 1), (514339818439, 1), (50762704307089, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_6113, prime_oneHundredThirtyFiveEC_514339818439, prime_oneHundredThirtyFiveEC_50762704307089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816024 : Nat.totient 159606029353881027714033816024 = 52685480264445042411684908160 := by
  rw [← show ((([(2, 3), (3, 1), (103, 1), (10420363, 1), (569667919, 1), (10876676611, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_103, prime_oneHundredThirtyFiveEC_10420363, prime_oneHundredThirtyFiveEC_569667919, prime_oneHundredThirtyFiveEC_10876676611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816025 : Nat.totient 159606029353881027714033816025 = 127684823483104822171227052800 := by
  rw [← show ((([(5, 2), (6384241174155241108561352641, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_6384241174155241108561352641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816026 : Nat.totient 159606029353881027714033816026 = 68402584008806154734585921148 := by
  rw [← show ((([(2, 1), (7, 1), (11400430668134359122430986859, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_11400430668134359122430986859]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816027 : Nat.totient 159606029353881027714033816027 = 106403844335819343569394710688 := by
  rw [← show ((([(3, 5), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_607213, prime_oneHundredThirtyFiveEC_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816028 : Nat.totient 159606029353881027714033816028 = 76904859420696960844448108544 := by
  rw [← show ((([(2, 2), (43, 1), (89, 1), (463, 1), (26800160419, 1), (840257611553, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_43, prime_oneHundredThirtyFiveEC_89, prime_oneHundredThirtyFiveEC_463, prime_oneHundredThirtyFiveEC_26800160419, prime_oneHundredThirtyFiveEC_840257611553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816029 : Nat.totient 159606029353881027714033816029 = 145054881066852954513330094080 := by
  rw [← show ((([(11, 1), (4933, 1), (14387, 1), (72073, 1), (2836629724719233, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_4933, prime_oneHundredThirtyFiveEC_14387, prime_oneHundredThirtyFiveEC_72073, prime_oneHundredThirtyFiveEC_2836629724719233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816030 : Nat.totient 159606029353881027714033816030 = 42561607827689956315737713696 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_3662228970263, prime_oneHundredThirtyFiveEC_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816031 : Nat.totient 159606029353881027714033816031 = 159597076303488147194164272552 := by
  rw [← show ((([(17827, 1), (8953050392880519869525653, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_17827, prime_oneHundredThirtyFiveEC_8953050392880519869525653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816032 : Nat.totient 159606029353881027714033816032 = 68729390863262359182567014400 := by
  rw [← show ((([(2, 5), (17, 1), (23, 1), (29, 1), (109, 1), (4035506599621491560801, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_23, prime_oneHundredThirtyFiveEC_29, prime_oneHundredThirtyFiveEC_109, prime_oneHundredThirtyFiveEC_4035506599621491560801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816033 : Nat.totient 159606029353881027714033816033 = 84187775481553563872198065920 := by
  rw [← show ((([(3, 1), (7, 1), (13, 2), (4476319, 1), (59550461, 1), (168708567463, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_4476319, prime_oneHundredThirtyFiveEC_59550461, prime_oneHundredThirtyFiveEC_168708567463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816034 : Nat.totient 159606029353881027714033816034 = 79801639867554261412470718464 := by
  rw [← show ((([(2, 1), (58049, 1), (1405726849, 1), (977965682448817, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_58049, prime_oneHundredThirtyFiveEC_1405726849, prime_oneHundredThirtyFiveEC_977965682448817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816035 : Nat.totient 159606029353881027714033816035 = 120421557502510239886024137600 := by
  rw [← show ((([(5, 1), (19, 1), (223, 1), (211231, 1), (35666719808417469181, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_19, prime_oneHundredThirtyFiveEC_223, prime_oneHundredThirtyFiveEC_211231, prime_oneHundredThirtyFiveEC_35666719808417469181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816036 : Nat.totient 159606029353881027714033816036 = 51070164965190394969549094400 := by
  rw [← show ((([(2, 2), (3, 2), (53, 1), (71, 1), (131, 1), (8993759679696815118617, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_53, prime_oneHundredThirtyFiveEC_71, prime_oneHundredThirtyFiveEC_131, prime_oneHundredThirtyFiveEC_8993759679696815118617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816037 : Nat.totient 159606029353881027714033816037 = 159606029353822109324419624416 := by
  rw [← show ((([(2709058570633, 1), (58915680555620989, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2709058570633, prime_oneHundredThirtyFiveEC_58915680555620989]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816038 : Nat.totient 159606029353881027714033816038 = 79803014676938786512801776280 := by
  rw [← show ((([(2, 1), (47506380087479, 1), (1679837835044261, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_47506380087479, prime_oneHundredThirtyFiveEC_1679837835044261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816039 : Nat.totient 159606029353881027714033816039 = 106027747320038764628679591936 := by
  rw [← show ((([(3, 1), (389, 1), (1033, 1), (132396991279118172886049, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_389, prime_oneHundredThirtyFiveEC_1033, prime_oneHundredThirtyFiveEC_132396991279118172886049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816040 : Nat.totient 159606029353881027714033816040 = 49747205732948037865906329600 := by
  rw [← show ((([(2, 3), (5, 1), (7, 1), (11, 1), (388373, 1), (133428789850506403081, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_388373, prime_oneHundredThirtyFiveEC_133428789850506403081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816041 : Nat.totient 159606029353881027714033816041 = 158592017032574941539816537600 := by
  rw [← show ((([(181, 1), (1559, 1), (7741, 1), (16007, 1), (4564756240143017, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_181, prime_oneHundredThirtyFiveEC_1559, prime_oneHundredThirtyFiveEC_7741, prime_oneHundredThirtyFiveEC_16007, prime_oneHundredThirtyFiveEC_4564756240143017]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816042 : Nat.totient 159606029353881027714033816042 = 52070015618123607416977479984 := by
  rw [← show ((([(2, 1), (3, 1), (47, 1), (1426127, 1), (396864253671680020903, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_47, prime_oneHundredThirtyFiveEC_1426127, prime_oneHundredThirtyFiveEC_396864253671680020903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816043 : Nat.totient 159606029353881027714033816043 = 159606029353881027714033816042 := by
  rw [← show ((([(159606029353881027714033816043, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_159606029353881027714033816043]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816044 : Nat.totient 159606029353881027714033816044 = 78450414085683083755961173440 := by
  rw [← show ((([(2, 2), (59, 1), (11014981, 1), (61397902960553752909, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_59, prime_oneHundredThirtyFiveEC_11014981, prime_oneHundredThirtyFiveEC_61397902960553752909]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816045 : Nat.totient 159606029353881027714033816045 = 82819931676784100601026153472 := by
  rw [← show ((([(3, 2), (5, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_37, prime_oneHundredThirtyFiveEC_31177, prime_oneHundredThirtyFiveEC_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816046 : Nat.totient 159606029353881027714033816046 = 73645581906434350889319902400 := by
  rw [← show ((([(2, 1), (13, 1), (3931, 1), (1561611151535927711817641, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_3931, prime_oneHundredThirtyFiveEC_1561611151535927711817641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816047 : Nat.totient 159606029353881027714033816047 = 136804396278241715298795636480 := by
  rw [← show ((([(7, 1), (177269, 1), (85915003129, 1), (1497095305021, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_177269, prime_oneHundredThirtyFiveEC_85915003129, prime_oneHundredThirtyFiveEC_1497095305021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816048 : Nat.totient 159606029353881027714033816048 = 53202009784348441490782544064 := by
  rw [← show ((([(2, 4), (3, 1), (190986192499, 1), (17410293215602999, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_190986192499, prime_oneHundredThirtyFiveEC_17410293215602999]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816049 : Nat.totient 159606029353881027714033816049 = 150167747280024147641656066560 := by
  rw [← show ((([(17, 1), (3023, 1), (250145449, 1), (12415654507405111, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_3023, prime_oneHundredThirtyFiveEC_250145449, prime_oneHundredThirtyFiveEC_12415654507405111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816050 : Nat.totient 159606029353881027714033816050 = 60987945438902918486816251200 := by
  rw [← show ((([(2, 1), (5, 2), (31, 1), (79, 1), (4703, 1), (277150409895147902543, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_31, prime_oneHundredThirtyFiveEC_79, prime_oneHundredThirtyFiveEC_4703, prime_oneHundredThirtyFiveEC_277150409895147902543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816051 : Nat.totient 159606029353881027714033816051 = 96443891483493262958354595840 := by
  rw [← show ((([(3, 1), (11, 1), (337, 1), (15289244417, 1), (938684030126243, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_337, prime_oneHundredThirtyFiveEC_15289244417, prime_oneHundredThirtyFiveEC_938684030126243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816052 : Nat.totient 159606029353881027714033816052 = 79802775812269069257716472960 := by
  rw [← show ((([(2, 2), (334093, 1), (119432335722299649883441, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_334093, prime_oneHundredThirtyFiveEC_119432335722299649883441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816053 : Nat.totient 159606029353881027714033816053 = 158589430440798982951524046368 := by
  rw [← show ((([(157, 1), (1016598913082044762509769529, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_157, prime_oneHundredThirtyFiveEC_1016598913082044762509769529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816054 : Nat.totient 159606029353881027714033816054 = 42041764496964066120448081920 := by
  rw [← show ((([(2, 1), (3, 3), (7, 1), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_19, prime_oneHundredThirtyFiveEC_41, prime_oneHundredThirtyFiveEC_397, prime_oneHundredThirtyFiveEC_13617913, prime_oneHundredThirtyFiveEC_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816055 : Nat.totient 159606029353881027714033816055 = 122133229434430757473255543680 := by
  rw [← show ((([(5, 1), (23, 1), (1602869, 1), (32246411, 1), (26851715585323, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_23, prime_oneHundredThirtyFiveEC_1602869, prime_oneHundredThirtyFiveEC_32246411, prime_oneHundredThirtyFiveEC_26851715585323]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816056 : Nat.totient 159606029353881027714033816056 = 79803014676940513857016908024 := by
  rw [← show ((([(2, 3), (19950753669235128464254227007, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_19950753669235128464254227007]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816057 : Nat.totient 159606029353881027714033816057 = 106404019569254018476022544036 := by
  rw [← show ((([(3, 1), (53202009784627009238011272019, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_53202009784627009238011272019]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816058 : Nat.totient 159606029353881027714033816058 = 79174639317998267884096510464 := by
  rw [← show ((([(2, 1), (127, 1), (15571489, 1), (1014344069, 1), (39783239047, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_127, prime_oneHundredThirtyFiveEC_15571489, prime_oneHundredThirtyFiveEC_1014344069, prime_oneHundredThirtyFiveEC_39783239047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816059 : Nat.totient 159606029353881027714033816059 = 147328638295226454360463298976 := by
  rw [← show ((([(13, 1), (35201629, 1), (348773259140236483667, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_35201629, prime_oneHundredThirtyFiveEC_348773259140236483667]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816060 : Nat.totient 159606029353881027714033816060 = 42537685526189720684367494400 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_2411, prime_oneHundredThirtyFiveEC_7039, prime_oneHundredThirtyFiveEC_188911, prime_oneHundredThirtyFiveEC_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816061 : Nat.totient 159606029353881027714033816061 = 131523546573912821590875029760 := by
  rw [← show ((([(7, 1), (29, 1), (239, 1), (14947, 1), (48119, 1), (4573879583189381, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_29, prime_oneHundredThirtyFiveEC_239, prime_oneHundredThirtyFiveEC_14947, prime_oneHundredThirtyFiveEC_48119, prime_oneHundredThirtyFiveEC_4573879583189381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816062 : Nat.totient 159606029353881027714033816062 = 72548195160855012597288098200 := by
  rw [← show ((([(2, 1), (11, 1), (7254819516085501259728809821, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_7254819516085501259728809821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816063 : Nat.totient 159606029353881027714033816063 = 106310592715413396052017907200 := by
  rw [← show ((([(3, 2), (1697, 1), (3461, 1), (3019418713742564280571, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_1697, prime_oneHundredThirtyFiveEC_3461, prime_oneHundredThirtyFiveEC_3019418713742564280571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816064 : Nat.totient 159606029353881027714033816064 = 79803014524433638828682019840 := by
  rw [← show ((([(2, 9), (523274867, 1), (595729980056158291, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_523274867, prime_oneHundredThirtyFiveEC_595729980056158291]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816065 : Nat.totient 159606029353881027714033816065 = 127684813941993876591448728576 := by
  rw [← show ((([(5, 1), (13680577, 1), (614504323, 1), (3797081613103, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_13680577, prime_oneHundredThirtyFiveEC_614504323, prime_oneHundredThirtyFiveEC_3797081613103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816066 : Nat.totient 159606029353881027714033816066 = 50072479797260934222895750400 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (1429468943351, 1), (1094647771778333, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_1429468943351, prime_oneHundredThirtyFiveEC_1094647771778333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816067 : Nat.totient 159606029353881027714033816067 = 159605958874067515650024398880 := by
  rw [← show ((([(3670123, 1), (5913109, 1), (7354493853937381, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3670123, prime_oneHundredThirtyFiveEC_5913109, prime_oneHundredThirtyFiveEC_7354493853937381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816068 : Nat.totient 159606029353881027714033816068 = 68402583777172620779482095648 := by
  rw [← show ((([(2, 2), (7, 3), (295305187, 1), (393934581260993837, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_295305187, prime_oneHundredThirtyFiveEC_393934581260993837]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816069 : Nat.totient 159606029353881027714033816069 = 105307070913900884264929527936 := by
  rw [← show ((([(3, 1), (97, 1), (548474327676567105546507959, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_97, prime_oneHundredThirtyFiveEC_548474327676567105546507959]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816070 : Nat.totient 159606029353881027714033816070 = 63842411741552411085613526424 := by
  rw [← show ((([(2, 1), (5, 1), (15960602935388102771403381607, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_15960602935388102771403381607]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816071 : Nat.totient 159606029353881027714033816071 = 155893910219734853802157837560 := by
  rw [← show ((([(43, 1), (444131, 1), (8357372316971481634087, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_43, prime_oneHundredThirtyFiveEC_444131, prime_oneHundredThirtyFiveEC_8357372316971481634087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816072 : Nat.totient 159606029353881027714033816072 = 48360795918978929800939531776 := by
  rw [← show ((([(2, 3), (3, 2), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_67, prime_oneHundredThirtyFiveEC_3067, prime_oneHundredThirtyFiveEC_829821849978416232493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816073 : Nat.totient 159606029353881027714033816073 = 137459737817494421666008510080 := by
  rw [← show ((([(11, 2), (19, 1), (359823089, 1), (192939564814238843, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_19, prime_oneHundredThirtyFiveEC_359823089, prime_oneHundredThirtyFiveEC_192939564814238843]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816074 : Nat.totient 159606029353881027714033816074 = 79761034961770982389257792000 := by
  rw [← show ((([(2, 1), (1901, 1), (357725681, 1), (117351072154346377, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_1901, prime_oneHundredThirtyFiveEC_357725681, prime_oneHundredThirtyFiveEC_117351072154346377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816075 : Nat.totient 159606029353881027714033816075 = 72959261139828998860439754240 := by
  rw [← show ((([(3, 1), (5, 2), (7, 1), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_28403, prime_oneHundredThirtyFiveEC_79847, prime_oneHundredThirtyFiveEC_5816549, prime_oneHundredThirtyFiveEC_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816076 : Nat.totient 159606029353881027714033816076 = 79012705809125591582347459200 := by
  rw [← show ((([(2, 2), (101, 1), (438937, 1), (900048136962172065887, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_101, prime_oneHundredThirtyFiveEC_438937, prime_oneHundredThirtyFiveEC_900048136962172065887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816077 : Nat.totient 159606029353881027714033816077 = 156989537069391174800688999360 := by
  rw [← show ((([(61, 1), (2616492284489852913344816657, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_61, prime_oneHundredThirtyFiveEC_2616492284489852913344816657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816078 : Nat.totient 159606029353881027714033816078 = 50670471648099202869029119488 := by
  rw [← show ((([(2, 1), (3, 1), (23, 1), (233, 1), (717281353, 1), (6920297186628619, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_23, prime_oneHundredThirtyFiveEC_233, prime_oneHundredThirtyFiveEC_717281353, prime_oneHundredThirtyFiveEC_6920297186628619]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816079 : Nat.totient 159606029353881027714033816079 = 159602741152036039539005150680 := by
  rw [← show ((([(48539, 1), (3288201844988175028616861, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_48539, prime_oneHundredThirtyFiveEC_3288201844988175028616861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816080 : Nat.totient 159606029353881027714033816080 = 63419612296819311859553241600 := by
  rw [← show ((([(2, 4), (5, 1), (151, 1), (31458437, 1), (419996061740133023, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_151, prime_oneHundredThirtyFiveEC_31458437, prime_oneHundredThirtyFiveEC_419996061740133023]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816081 : Nat.totient 159606029353881027714033816081 = 102971603230106497287696529920 := by
  rw [← show ((([(3, 3), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_31, prime_oneHundredThirtyFiveEC_3599009, prime_oneHundredThirtyFiveEC_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816082 : Nat.totient 159606029353881027714033816082 = 66017987663724743917460622336 := by
  rw [← show ((([(2, 1), (7, 1), (37, 1), (269, 1), (293, 1), (1063, 1), (3677615903539239269, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_37, prime_oneHundredThirtyFiveEC_269, prime_oneHundredThirtyFiveEC_293, prime_oneHundredThirtyFiveEC_1063, prime_oneHundredThirtyFiveEC_3677615903539239269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816083 : Nat.totient 159606029353881027714033816083 = 150217185409497254848958423040 := by
  rw [← show ((([(17, 1), (937241, 1), (1603067, 1), (6248811431728417, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_937241, prime_oneHundredThirtyFiveEC_1603067, prime_oneHundredThirtyFiveEC_6248811431728417]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816084 : Nat.totient 159606029353881027714033816084 = 48345078510076481045279539200 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (4133, 1), (5569, 1), (52533064873537140481, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_4133, prime_oneHundredThirtyFiveEC_5569, prime_oneHundredThirtyFiveEC_52533064873537140481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816085 : Nat.totient 159606029353881027714033816085 = 117486355153783350751799956992 := by
  rw [← show ((([(5, 1), (13, 1), (313, 1), (7844975637939593399559293, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_313, prime_oneHundredThirtyFiveEC_7844975637939593399559293]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816086 : Nat.totient 159606029353881027714033816086 = 79802676804189462590314377000 := by
  rw [← show ((([(2, 1), (260011, 1), (2578351, 1), (119037976864322863, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_260011, prime_oneHundredThirtyFiveEC_2578351, prime_oneHundredThirtyFiveEC_119037976864322863]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816087 : Nat.totient 159606029353881027714033816087 = 106403977322284719326754170040 := by
  rw [← show ((([(3, 1), (2518619, 1), (21123484649574631668391, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_2518619, prime_oneHundredThirtyFiveEC_21123484649574631668391]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816088 : Nat.totient 159606029353881027714033816088 = 77850498636021216235346012160 := by
  rw [← show ((([(2, 3), (73, 1), (107, 1), (631, 1), (533999, 1), (7580238420295529, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_73, prime_oneHundredThirtyFiveEC_107, prime_oneHundredThirtyFiveEC_631, prime_oneHundredThirtyFiveEC_533999, prime_oneHundredThirtyFiveEC_7580238420295529]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816089 : Nat.totient 159606029353881027714033816089 = 131368109953851405599836847040 := by
  rw [← show ((([(7, 1), (47, 1), (53, 1), (106211754007, 1), (86179693454171, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_47, prime_oneHundredThirtyFiveEC_53, prime_oneHundredThirtyFiveEC_106211754007, prime_oneHundredThirtyFiveEC_86179693454171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816090 : Nat.totient 159606029353881027714033816090 = 40639589391783839901740040192 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_29, prime_oneHundredThirtyFiveEC_113, prime_oneHundredThirtyFiveEC_449, prime_oneHundredThirtyFiveEC_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816091 : Nat.totient 159606029353881027714033816091 = 159420611218057539577302491136 := by
  rw [← show ((([(929, 1), (17077, 1), (37277, 1), (166741177, 1), (1618594963, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_929, prime_oneHundredThirtyFiveEC_17077, prime_oneHundredThirtyFiveEC_37277, prime_oneHundredThirtyFiveEC_166741177, prime_oneHundredThirtyFiveEC_1618594963]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816092 : Nat.totient 159606029353881027714033816092 = 75602856006019976136249995136 := by
  rw [← show ((([(2, 2), (19, 1), (20360887289, 1), (103142820044894053, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_19, prime_oneHundredThirtyFiveEC_20360887289, prime_oneHundredThirtyFiveEC_103142820044894053]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816093 : Nat.totient 159606029353881027714033816093 = 106404018992366114912584177728 := by
  rw [← show ((([(3, 1), (184444879, 1), (288443951781534738289, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_184444879, prime_oneHundredThirtyFiveEC_288443951781534738289]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816094 : Nat.totient 159606029353881027714033816094 = 79686172349703308013610423680 := by
  rw [← show ((([(2, 1), (683, 1), (184602589, 1), (632937469657326481, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_683, prime_oneHundredThirtyFiveEC_184602589, prime_oneHundredThirtyFiveEC_632937469657326481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816095 : Nat.totient 159606029353881027714033816095 = 113082076111092349592185632000 := by
  rw [← show ((([(5, 1), (11, 1), (41, 1), (691, 1), (102429416767293794920459, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_11, prime_oneHundredThirtyFiveEC_41, prime_oneHundredThirtyFiveEC_691, prime_oneHundredThirtyFiveEC_102429416767293794920459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816096 : Nat.totient 159606029353881027714033816096 = 45601501800668787394972581888 := by
  rw [← show ((([(2, 5), (3, 1), (7, 1), (216373, 1), (4507537, 1), (243521692501993, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_7, prime_oneHundredThirtyFiveEC_216373, prime_oneHundredThirtyFiveEC_4507537, prime_oneHundredThirtyFiveEC_243521692501993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816097 : Nat.totient 159606029353881027714033816097 = 159200922052229194882794132000 := by
  rw [← show ((([(457, 1), (2851, 1), (122499940021721448817171, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_457, prime_oneHundredThirtyFiveEC_2851, prime_oneHundredThirtyFiveEC_122499940021721448817171]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816098 : Nat.totient 159606029353881027714033816098 = 72776758249663607969844004800 := by
  rw [← show ((([(2, 1), (13, 1), (83, 1), (1772971, 1), (41715381632189132261, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_13, prime_oneHundredThirtyFiveEC_83, prime_oneHundredThirtyFiveEC_1772971, prime_oneHundredThirtyFiveEC_41715381632189132261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816099 : Nat.totient 159606029353881027714033816099 = 106027043363723070400063530240 := by
  rw [← show ((([(3, 2), (283, 1), (107071, 1), (11129533489, 1), (52586168543, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_3, prime_oneHundredThirtyFiveEC_283, prime_oneHundredThirtyFiveEC_107071, prime_oneHundredThirtyFiveEC_11129533489, prime_oneHundredThirtyFiveEC_52586168543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816100 : Nat.totient 159606029353881027714033816100 = 60086472858853805509616373760 := by
  rw [← show ((([(2, 2), (5, 2), (17, 1), (168263, 1), (412127, 1), (1353881570594633, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_2, prime_oneHundredThirtyFiveEC_5, prime_oneHundredThirtyFiveEC_17, prime_oneHundredThirtyFiveEC_168263, prime_oneHundredThirtyFiveEC_412127, prime_oneHundredThirtyFiveEC_1353881570594633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredThirtyFiveEC_159606029353881027714033816101 : Nat.totient 159606029353881027714033816101 = 152419203002170085799491655520 := by
  rw [← show ((([(23, 1), (617, 1), (11246989595791771384260011, 1)] : List FactorBlock).map factorBlockValue).prod) = 159606029353881027714033816101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredThirtyFiveEC_23, prime_oneHundredThirtyFiveEC_617, prime_oneHundredThirtyFiveEC_11246989595791771384260011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredThirtyFiveEC : certifiedKill 1 159606029353881027714033815999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816000, phi_oneHundredThirtyFiveEC_159606029353881027714033816001, phi_oneHundredThirtyFiveEC_159606029353881027714033816002,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816003, phi_oneHundredThirtyFiveEC_159606029353881027714033816004, phi_oneHundredThirtyFiveEC_159606029353881027714033816005,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816006, phi_oneHundredThirtyFiveEC_159606029353881027714033816007, phi_oneHundredThirtyFiveEC_159606029353881027714033816008,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816009, phi_oneHundredThirtyFiveEC_159606029353881027714033816010, phi_oneHundredThirtyFiveEC_159606029353881027714033816011,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816012, phi_oneHundredThirtyFiveEC_159606029353881027714033816013, phi_oneHundredThirtyFiveEC_159606029353881027714033816014,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816015, phi_oneHundredThirtyFiveEC_159606029353881027714033816016, phi_oneHundredThirtyFiveEC_159606029353881027714033816017,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816018, phi_oneHundredThirtyFiveEC_159606029353881027714033816019, phi_oneHundredThirtyFiveEC_159606029353881027714033816020,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816021, phi_oneHundredThirtyFiveEC_159606029353881027714033816022, phi_oneHundredThirtyFiveEC_159606029353881027714033816023,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816024, phi_oneHundredThirtyFiveEC_159606029353881027714033816025, phi_oneHundredThirtyFiveEC_159606029353881027714033816026,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816027, phi_oneHundredThirtyFiveEC_159606029353881027714033816028, phi_oneHundredThirtyFiveEC_159606029353881027714033816029,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816030, phi_oneHundredThirtyFiveEC_159606029353881027714033816031, phi_oneHundredThirtyFiveEC_159606029353881027714033816032,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816033, phi_oneHundredThirtyFiveEC_159606029353881027714033816034, phi_oneHundredThirtyFiveEC_159606029353881027714033816035,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816036, phi_oneHundredThirtyFiveEC_159606029353881027714033816037, phi_oneHundredThirtyFiveEC_159606029353881027714033816038,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816039, phi_oneHundredThirtyFiveEC_159606029353881027714033816040, phi_oneHundredThirtyFiveEC_159606029353881027714033816041,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816042, phi_oneHundredThirtyFiveEC_159606029353881027714033816043, phi_oneHundredThirtyFiveEC_159606029353881027714033816044,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816045, phi_oneHundredThirtyFiveEC_159606029353881027714033816046, phi_oneHundredThirtyFiveEC_159606029353881027714033816047,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816048, phi_oneHundredThirtyFiveEC_159606029353881027714033816049, phi_oneHundredThirtyFiveEC_159606029353881027714033816050,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816051, phi_oneHundredThirtyFiveEC_159606029353881027714033816052, phi_oneHundredThirtyFiveEC_159606029353881027714033816053,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816054, phi_oneHundredThirtyFiveEC_159606029353881027714033816055, phi_oneHundredThirtyFiveEC_159606029353881027714033816056,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816057, phi_oneHundredThirtyFiveEC_159606029353881027714033816058, phi_oneHundredThirtyFiveEC_159606029353881027714033816059,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816060, phi_oneHundredThirtyFiveEC_159606029353881027714033816061, phi_oneHundredThirtyFiveEC_159606029353881027714033816062,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816063, phi_oneHundredThirtyFiveEC_159606029353881027714033816064, phi_oneHundredThirtyFiveEC_159606029353881027714033816065,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816066, phi_oneHundredThirtyFiveEC_159606029353881027714033816067, phi_oneHundredThirtyFiveEC_159606029353881027714033816068,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816069, phi_oneHundredThirtyFiveEC_159606029353881027714033816070, phi_oneHundredThirtyFiveEC_159606029353881027714033816071,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816072, phi_oneHundredThirtyFiveEC_159606029353881027714033816073, phi_oneHundredThirtyFiveEC_159606029353881027714033816074,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816075, phi_oneHundredThirtyFiveEC_159606029353881027714033816076, phi_oneHundredThirtyFiveEC_159606029353881027714033816077,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816078, phi_oneHundredThirtyFiveEC_159606029353881027714033816079, phi_oneHundredThirtyFiveEC_159606029353881027714033816080,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816081, phi_oneHundredThirtyFiveEC_159606029353881027714033816082, phi_oneHundredThirtyFiveEC_159606029353881027714033816083,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816084, phi_oneHundredThirtyFiveEC_159606029353881027714033816085, phi_oneHundredThirtyFiveEC_159606029353881027714033816086,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816087, phi_oneHundredThirtyFiveEC_159606029353881027714033816088, phi_oneHundredThirtyFiveEC_159606029353881027714033816089,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816090, phi_oneHundredThirtyFiveEC_159606029353881027714033816091, phi_oneHundredThirtyFiveEC_159606029353881027714033816092,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816093, phi_oneHundredThirtyFiveEC_159606029353881027714033816094, phi_oneHundredThirtyFiveEC_159606029353881027714033816095,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816096, phi_oneHundredThirtyFiveEC_159606029353881027714033816097, phi_oneHundredThirtyFiveEC_159606029353881027714033816098,
    phi_oneHundredThirtyFiveEC_159606029353881027714033816099, phi_oneHundredThirtyFiveEC_159606029353881027714033816100, phi_oneHundredThirtyFiveEC_159606029353881027714033816101
    ]

end TotientTailPeriodKiller
end Erdos249257
