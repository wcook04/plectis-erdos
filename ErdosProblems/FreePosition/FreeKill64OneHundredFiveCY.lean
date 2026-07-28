import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredFiveCYFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiveCYFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiveCYFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiveCYFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiveCYFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiveCYFastPow a n * oneHundredFiveCYFastPow a n * a else oneHundredFiveCYFastPow a n * oneHundredFiveCYFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiveCY_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiveCY_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiveCY_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiveCY_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiveCY_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiveCY_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiveCY_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiveCY_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiveCY_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiveCY_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiveCY_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiveCY_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiveCY_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiveCY_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiveCY_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiveCY_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiveCY_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiveCY_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiveCY_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiveCY_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiveCY_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiveCY_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiveCY_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiveCY_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiveCY_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiveCY_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiveCY_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiveCY_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiveCY_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiveCY_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiveCY_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiveCY_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiveCY_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiveCY_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiveCY_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiveCY_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiveCY_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiveCY_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiveCY_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiveCY_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredFiveCY_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiveCY_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiveCY_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiveCY_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiveCY_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiveCY_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiveCY_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiveCY_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiveCY_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFiveCY_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiveCY_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFiveCY_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiveCY_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiveCY_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiveCY_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFiveCY_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiveCY_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiveCY_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiveCY_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredFiveCY_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFiveCY_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiveCY_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiveCY_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiveCY_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiveCY_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFiveCY_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFiveCY_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiveCY_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredFiveCY_419 : Nat.Prime 419 := by norm_num

private theorem prime_oneHundredFiveCY_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFiveCY_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredFiveCY_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredFiveCY_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredFiveCY_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiveCY_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFiveCY_487 : Nat.Prime 487 := by norm_num

private theorem prime_oneHundredFiveCY_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredFiveCY_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiveCY_521 : Nat.Prime 521 := by norm_num

private theorem prime_oneHundredFiveCY_523 : Nat.Prime 523 := by norm_num

private theorem prime_oneHundredFiveCY_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFiveCY_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFiveCY_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredFiveCY_599 : Nat.Prime 599 := by norm_num

private theorem prime_oneHundredFiveCY_601 : Nat.Prime 601 := by norm_num

private theorem prime_oneHundredFiveCY_613 : Nat.Prime 613 := by norm_num

private theorem prime_oneHundredFiveCY_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredFiveCY_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFiveCY_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFiveCY_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredFiveCY_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredFiveCY_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFiveCY_739 : Nat.Prime 739 := by norm_num

private theorem prime_oneHundredFiveCY_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFiveCY_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredFiveCY_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFiveCY_853 : Nat.Prime 853 := by norm_num

private theorem prime_oneHundredFiveCY_887 : Nat.Prime 887 := by norm_num

private theorem prime_oneHundredFiveCY_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiveCY_947 : Nat.Prime 947 := by norm_num

private theorem prime_oneHundredFiveCY_1009 : Nat.Prime 1009 := by norm_num

private theorem prime_oneHundredFiveCY_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFiveCY_1033 : Nat.Prime 1033 := by norm_num

private theorem prime_oneHundredFiveCY_1049 : Nat.Prime 1049 := by norm_num

private theorem prime_oneHundredFiveCY_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredFiveCY_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFiveCY_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredFiveCY_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredFiveCY_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredFiveCY_1129 : Nat.Prime 1129 := by norm_num

private theorem prime_oneHundredFiveCY_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredFiveCY_1187 : Nat.Prime 1187 := by norm_num

private theorem prime_oneHundredFiveCY_1193 : Nat.Prime 1193 := by norm_num

private theorem prime_oneHundredFiveCY_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFiveCY_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredFiveCY_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFiveCY_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFiveCY_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredFiveCY_1373 : Nat.Prime 1373 := by norm_num

private theorem prime_oneHundredFiveCY_1439 : Nat.Prime 1439 := by norm_num

private theorem prime_oneHundredFiveCY_1447 : Nat.Prime 1447 := by norm_num

private theorem prime_oneHundredFiveCY_1499 : Nat.Prime 1499 := by norm_num

private theorem prime_oneHundredFiveCY_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredFiveCY_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredFiveCY_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredFiveCY_1597 : Nat.Prime 1597 := by norm_num

private theorem prime_oneHundredFiveCY_1697 : Nat.Prime 1697 := by norm_num

private theorem prime_oneHundredFiveCY_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredFiveCY_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredFiveCY_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredFiveCY_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredFiveCY_2063 : Nat.Prime 2063 := by norm_num

private theorem prime_oneHundredFiveCY_2129 : Nat.Prime 2129 := by norm_num

private theorem prime_oneHundredFiveCY_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredFiveCY_2141 : Nat.Prime 2141 := by norm_num

private theorem prime_oneHundredFiveCY_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredFiveCY_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredFiveCY_2281 : Nat.Prime 2281 := by norm_num

private theorem prime_oneHundredFiveCY_2297 : Nat.Prime 2297 := by norm_num

private theorem prime_oneHundredFiveCY_2309 : Nat.Prime 2309 := by norm_num

private theorem prime_oneHundredFiveCY_2381 : Nat.Prime 2381 := by norm_num

private theorem prime_oneHundredFiveCY_2459 : Nat.Prime 2459 := by norm_num

private theorem prime_oneHundredFiveCY_2477 : Nat.Prime 2477 := by norm_num

private theorem prime_oneHundredFiveCY_2593 : Nat.Prime 2593 := by norm_num

private theorem prime_oneHundredFiveCY_2617 : Nat.Prime 2617 := by norm_num

private theorem prime_oneHundredFiveCY_2663 : Nat.Prime 2663 := by norm_num

private theorem prime_oneHundredFiveCY_2753 : Nat.Prime 2753 := by norm_num

private theorem prime_oneHundredFiveCY_2801 : Nat.Prime 2801 := by norm_num

private theorem prime_oneHundredFiveCY_3067 : Nat.Prime 3067 := by norm_num

private theorem prime_oneHundredFiveCY_3109 : Nat.Prime 3109 := by norm_num

private theorem prime_oneHundredFiveCY_3433 : Nat.Prime 3433 := by norm_num

private theorem prime_oneHundredFiveCY_3449 : Nat.Prime 3449 := by norm_num

private theorem prime_oneHundredFiveCY_3461 : Nat.Prime 3461 := by norm_num

private theorem prime_oneHundredFiveCY_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_oneHundredFiveCY_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredFiveCY_3719 : Nat.Prime 3719 := by norm_num

private theorem prime_oneHundredFiveCY_3739 : Nat.Prime 3739 := by norm_num

private theorem prime_oneHundredFiveCY_3793 : Nat.Prime 3793 := by norm_num

private theorem prime_oneHundredFiveCY_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredFiveCY_3889 : Nat.Prime 3889 := by norm_num

private theorem prime_oneHundredFiveCY_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredFiveCY_4003 : Nat.Prime 4003 := by norm_num

private theorem prime_oneHundredFiveCY_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_oneHundredFiveCY_4091 : Nat.Prime 4091 := by norm_num

private theorem prime_oneHundredFiveCY_4153 : Nat.Prime 4153 := by norm_num

private theorem prime_oneHundredFiveCY_4349 : Nat.Prime 4349 := by norm_num

private theorem prime_oneHundredFiveCY_4363 : Nat.Prime 4363 := by norm_num

private theorem prime_oneHundredFiveCY_4421 : Nat.Prime 4421 := by norm_num

private theorem prime_oneHundredFiveCY_4457 : Nat.Prime 4457 := by norm_num

private theorem prime_oneHundredFiveCY_4481 : Nat.Prime 4481 := by norm_num

private theorem prime_oneHundredFiveCY_4621 : Nat.Prime 4621 := by norm_num

private theorem prime_oneHundredFiveCY_4639 : Nat.Prime 4639 := by norm_num

private theorem prime_oneHundredFiveCY_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredFiveCY_4759 : Nat.Prime 4759 := by norm_num

private theorem prime_oneHundredFiveCY_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredFiveCY_5231 : Nat.Prime 5231 := by norm_num

private theorem prime_oneHundredFiveCY_5233 : Nat.Prime 5233 := by norm_num

private theorem prime_oneHundredFiveCY_5273 : Nat.Prime 5273 := by norm_num

private theorem prime_oneHundredFiveCY_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredFiveCY_5437 : Nat.Prime 5437 := by norm_num

private theorem prime_oneHundredFiveCY_5441 : Nat.Prime 5441 := by norm_num

private theorem prime_oneHundredFiveCY_5573 : Nat.Prime 5573 := by norm_num

private theorem prime_oneHundredFiveCY_5821 : Nat.Prime 5821 := by norm_num

private theorem prime_oneHundredFiveCY_5879 : Nat.Prime 5879 := by norm_num

private theorem prime_oneHundredFiveCY_6133 : Nat.Prime 6133 := by norm_num

private theorem prime_oneHundredFiveCY_6211 : Nat.Prime 6211 := by norm_num

private theorem prime_oneHundredFiveCY_6679 : Nat.Prime 6679 := by norm_num

private theorem prime_oneHundredFiveCY_6703 : Nat.Prime 6703 := by norm_num

private theorem prime_oneHundredFiveCY_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredFiveCY_6883 : Nat.Prime 6883 := by norm_num

private theorem prime_oneHundredFiveCY_7297 : Nat.Prime 7297 := by norm_num

private theorem prime_oneHundredFiveCY_7517 : Nat.Prime 7517 := by norm_num

private theorem prime_oneHundredFiveCY_7673 : Nat.Prime 7673 := by norm_num

private theorem prime_oneHundredFiveCY_7907 : Nat.Prime 7907 := by norm_num

private theorem prime_oneHundredFiveCY_8317 : Nat.Prime 8317 := by norm_num

private theorem prime_oneHundredFiveCY_8377 : Nat.Prime 8377 := by norm_num

private theorem prime_oneHundredFiveCY_8839 : Nat.Prime 8839 := by norm_num

private theorem prime_oneHundredFiveCY_8933 : Nat.Prime 8933 := by norm_num

private theorem prime_oneHundredFiveCY_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredFiveCY_9803 : Nat.Prime 9803 := by norm_num

private theorem prime_oneHundredFiveCY_10457 : Nat.Prime 10457 := by norm_num

private theorem prime_oneHundredFiveCY_10723 : Nat.Prime 10723 := by norm_num

private theorem prime_oneHundredFiveCY_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredFiveCY_11593 : Nat.Prime 11593 := by norm_num

private theorem prime_oneHundredFiveCY_11933 : Nat.Prime 11933 := by norm_num

private theorem prime_oneHundredFiveCY_12101 : Nat.Prime 12101 := by norm_num

private theorem prime_oneHundredFiveCY_12539 : Nat.Prime 12539 := by norm_num

private theorem prime_oneHundredFiveCY_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredFiveCY_13109 : Nat.Prime 13109 := by norm_num

private theorem prime_oneHundredFiveCY_13121 : Nat.Prime 13121 := by norm_num

private theorem prime_oneHundredFiveCY_13151 : Nat.Prime 13151 := by norm_num

private theorem prime_oneHundredFiveCY_13421 : Nat.Prime 13421 := by norm_num

private theorem prime_oneHundredFiveCY_13933 : Nat.Prime 13933 := by norm_num

private theorem prime_oneHundredFiveCY_14029 : Nat.Prime 14029 := by norm_num

private theorem prime_oneHundredFiveCY_14389 : Nat.Prime 14389 := by norm_num

private theorem prime_oneHundredFiveCY_14437 : Nat.Prime 14437 := by norm_num

private theorem prime_oneHundredFiveCY_14591 : Nat.Prime 14591 := by norm_num

private theorem prime_oneHundredFiveCY_14621 : Nat.Prime 14621 := by norm_num

private theorem prime_oneHundredFiveCY_14737 : Nat.Prime 14737 := by norm_num

private theorem prime_oneHundredFiveCY_15061 : Nat.Prime 15061 := by norm_num

private theorem prime_oneHundredFiveCY_15259 : Nat.Prime 15259 := by norm_num

private theorem prime_oneHundredFiveCY_15269 : Nat.Prime 15269 := by norm_num

private theorem prime_oneHundredFiveCY_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiveCY_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredFiveCY_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredFiveCY_18181 : Nat.Prime 18181 := by norm_num

private theorem prime_oneHundredFiveCY_18251 : Nat.Prime 18251 := by norm_num

private theorem prime_oneHundredFiveCY_19471 : Nat.Prime 19471 := by norm_num

private theorem prime_oneHundredFiveCY_19489 : Nat.Prime 19489 := by norm_num

private theorem prime_oneHundredFiveCY_20051 : Nat.Prime 20051 := by norm_num

private theorem prime_oneHundredFiveCY_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiveCY_20899 : Nat.Prime 20899 := by norm_num

private theorem prime_oneHundredFiveCY_22541 : Nat.Prime 22541 := by norm_num

private theorem prime_oneHundredFiveCY_22699 : Nat.Prime 22699 := by norm_num

private theorem prime_oneHundredFiveCY_24223 : Nat.Prime 24223 := by norm_num

private theorem prime_oneHundredFiveCY_24571 : Nat.Prime 24571 := by norm_num

private theorem prime_oneHundredFiveCY_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredFiveCY_25189 : Nat.Prime 25189 := by norm_num

private theorem prime_oneHundredFiveCY_25243 : Nat.Prime 25243 := by norm_num

private theorem prime_oneHundredFiveCY_26449 : Nat.Prime 26449 := by norm_num

private theorem prime_oneHundredFiveCY_26591 : Nat.Prime 26591 := by norm_num

private theorem prime_oneHundredFiveCY_26927 : Nat.Prime 26927 := by norm_num

private theorem prime_oneHundredFiveCY_28163 : Nat.Prime 28163 := by norm_num

private theorem prime_oneHundredFiveCY_28591 : Nat.Prime 28591 := by norm_num

private theorem prime_oneHundredFiveCY_31033 : Nat.Prime 31033 := by norm_num

private theorem prime_oneHundredFiveCY_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredFiveCY_33721 : Nat.Prime 33721 := by norm_num

private theorem prime_oneHundredFiveCY_33757 : Nat.Prime 33757 := by norm_num

private theorem prime_oneHundredFiveCY_35129 : Nat.Prime 35129 := by norm_num

private theorem prime_oneHundredFiveCY_35267 : Nat.Prime 35267 := by norm_num

private theorem prime_oneHundredFiveCY_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredFiveCY_37019 : Nat.Prime 37019 := by norm_num

private theorem prime_oneHundredFiveCY_37357 : Nat.Prime 37357 := by norm_num

private theorem prime_oneHundredFiveCY_37567 : Nat.Prime 37567 := by norm_num

private theorem prime_oneHundredFiveCY_38677 : Nat.Prime 38677 := by norm_num

private theorem prime_oneHundredFiveCY_39551 : Nat.Prime 39551 := by norm_num

private theorem prime_oneHundredFiveCY_42467 : Nat.Prime 42467 := by norm_num

private theorem prime_oneHundredFiveCY_43271 : Nat.Prime 43271 := by norm_num

private theorem prime_oneHundredFiveCY_43711 : Nat.Prime 43711 := by norm_num

private theorem prime_oneHundredFiveCY_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredFiveCY_45481 : Nat.Prime 45481 := by norm_num

private theorem prime_oneHundredFiveCY_46381 : Nat.Prime 46381 := by norm_num

private theorem prime_oneHundredFiveCY_46591 : Nat.Prime 46591 := by norm_num

private theorem prime_oneHundredFiveCY_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredFiveCY_48131 : Nat.Prime 48131 := by norm_num

private theorem prime_oneHundredFiveCY_50341 : Nat.Prime 50341 := by norm_num

private theorem prime_oneHundredFiveCY_57383 : Nat.Prime 57383 := by norm_num

private theorem prime_oneHundredFiveCY_58963 : Nat.Prime 58963 := by norm_num

private theorem prime_oneHundredFiveCY_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredFiveCY_67231 : Nat.Prime 67231 := by norm_num

private theorem prime_oneHundredFiveCY_68113 : Nat.Prime 68113 := by norm_num

private theorem prime_oneHundredFiveCY_69877 : Nat.Prime 69877 := by norm_num

private theorem prime_oneHundredFiveCY_71569 : Nat.Prime 71569 := by norm_num

private theorem prime_oneHundredFiveCY_76163 : Nat.Prime 76163 := by norm_num

private theorem prime_oneHundredFiveCY_77687 : Nat.Prime 77687 := by norm_num

private theorem prime_oneHundredFiveCY_80039 : Nat.Prime 80039 := by norm_num

private theorem prime_oneHundredFiveCY_80603 : Nat.Prime 80603 := by norm_num

private theorem prime_oneHundredFiveCY_80783 : Nat.Prime 80783 := by norm_num

private theorem prime_oneHundredFiveCY_84673 : Nat.Prime 84673 := by norm_num

private theorem prime_oneHundredFiveCY_85847 : Nat.Prime 85847 := by norm_num

private theorem prime_oneHundredFiveCY_88609 : Nat.Prime 88609 := by norm_num

private theorem prime_oneHundredFiveCY_91331 : Nat.Prime 91331 := by norm_num

private theorem prime_oneHundredFiveCY_91513 : Nat.Prime 91513 := by norm_num

private theorem prime_oneHundredFiveCY_96281 : Nat.Prime 96281 := by norm_num

private theorem prime_oneHundredFiveCY_96857 : Nat.Prime 96857 := by norm_num

private theorem prime_oneHundredFiveCY_96973 : Nat.Prime 96973 := by norm_num

private theorem prime_oneHundredFiveCY_97453 : Nat.Prime 97453 := by norm_num

private theorem prime_oneHundredFiveCY_101027 : Nat.Prime 101027 := by norm_num

private theorem prime_oneHundredFiveCY_103981 : Nat.Prime 103981 := by norm_num

private theorem prime_oneHundredFiveCY_107071 : Nat.Prime 107071 := by norm_num

private theorem prime_oneHundredFiveCY_113357 : Nat.Prime 113357 := by norm_num

private theorem prime_oneHundredFiveCY_113537 : Nat.Prime 113537 := by norm_num

private theorem prime_oneHundredFiveCY_116443 : Nat.Prime 116443 := by norm_num

private theorem prime_oneHundredFiveCY_120623 : Nat.Prime 120623 := by norm_num

private theorem prime_oneHundredFiveCY_121439 : Nat.Prime 121439 := by norm_num

private theorem prime_oneHundredFiveCY_135119 : Nat.Prime 135119 := by norm_num

private theorem prime_oneHundredFiveCY_142433 : Nat.Prime 142433 := by norm_num

private theorem prime_oneHundredFiveCY_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredFiveCY_146933 : Nat.Prime 146933 := by norm_num

private theorem prime_oneHundredFiveCY_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredFiveCY_152597 : Nat.Prime 152597 := by norm_num

private theorem prime_oneHundredFiveCY_155801 : Nat.Prime 155801 := by norm_num

private theorem prime_oneHundredFiveCY_160541 : Nat.Prime 160541 := by norm_num

private theorem prime_oneHundredFiveCY_160813 : Nat.Prime 160813 := by norm_num

private theorem prime_oneHundredFiveCY_170389 : Nat.Prime 170389 := by norm_num

private theorem prime_oneHundredFiveCY_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiveCY_172171 : Nat.Prime 172171 := by norm_num

private theorem prime_oneHundredFiveCY_179989 : Nat.Prime 179989 := by norm_num

private theorem prime_oneHundredFiveCY_185153 : Nat.Prime 185153 := by norm_num

private theorem prime_oneHundredFiveCY_194483 : Nat.Prime 194483 := by norm_num

private theorem prime_oneHundredFiveCY_196081 : Nat.Prime 196081 := by norm_num

private theorem prime_oneHundredFiveCY_200789 : Nat.Prime 200789 := by norm_num

private theorem prime_oneHundredFiveCY_205837 : Nat.Prime 205837 := by norm_num

private theorem prime_oneHundredFiveCY_205913 : Nat.Prime 205913 := by norm_num

private theorem prime_oneHundredFiveCY_227719 : Nat.Prime 227719 := by norm_num

private theorem prime_oneHundredFiveCY_232681 : Nat.Prime 232681 := by norm_num

private theorem prime_oneHundredFiveCY_239069 : Nat.Prime 239069 := by norm_num

private theorem prime_oneHundredFiveCY_257273 : Nat.Prime 257273 := by norm_num

private theorem prime_oneHundredFiveCY_265709 : Nat.Prime 265709 := by norm_num

private theorem prime_oneHundredFiveCY_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredFiveCY_289103 : Nat.Prime 289103 := by norm_num

private theorem prime_oneHundredFiveCY_311743 : Nat.Prime 311743 := by norm_num

private theorem prime_oneHundredFiveCY_335009 : Nat.Prime 335009 := by norm_num

private theorem prime_oneHundredFiveCY_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredFiveCY_368077 : Nat.Prime 368077 := by norm_num

private theorem prime_oneHundredFiveCY_369469 : Nat.Prime 369469 := by norm_num

private theorem prime_oneHundredFiveCY_388187 : Nat.Prime 388187 := by norm_num

private theorem prime_oneHundredFiveCY_397379 : Nat.Prime 397379 := by norm_num

private theorem prime_oneHundredFiveCY_434039 : Nat.Prime 434039 := by norm_num

private theorem prime_oneHundredFiveCY_452957 : Nat.Prime 452957 := by norm_num

private theorem prime_oneHundredFiveCY_467941 : Nat.Prime 467941 := by norm_num

private theorem prime_oneHundredFiveCY_494959 : Nat.Prime 494959 := by norm_num

private theorem prime_oneHundredFiveCY_502001 : Nat.Prime 502001 := by norm_num

private theorem prime_oneHundredFiveCY_505823 : Nat.Prime 505823 := by norm_num

private theorem prime_oneHundredFiveCY_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredFiveCY_570881 : Nat.Prime 570881 := by norm_num

private theorem prime_oneHundredFiveCY_594023 : Nat.Prime 594023 := by norm_num

private theorem prime_oneHundredFiveCY_598447 : Nat.Prime 598447 := by norm_num

private theorem prime_oneHundredFiveCY_607213 : Nat.Prime 607213 := by norm_num

private theorem prime_oneHundredFiveCY_643781 : Nat.Prime 643781 := by norm_num

private theorem prime_oneHundredFiveCY_674879 : Nat.Prime 674879 := by norm_num

private theorem prime_oneHundredFiveCY_702239 : Nat.Prime 702239 := by norm_num

private theorem prime_oneHundredFiveCY_735479 : Nat.Prime 735479 := by norm_num

private theorem prime_oneHundredFiveCY_746371 : Nat.Prime 746371 := by norm_num

private theorem prime_oneHundredFiveCY_755137 : Nat.Prime 755137 := by norm_num

private theorem prime_oneHundredFiveCY_792107 : Nat.Prime 792107 := by norm_num

private theorem prime_oneHundredFiveCY_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredFiveCY_902389 : Nat.Prime 902389 := by norm_num

private theorem prime_oneHundredFiveCY_997813 : Nat.Prime 997813 := by norm_num

private theorem prime_oneHundredFiveCY_1079879 : Nat.Prime 1079879 := by norm_num

private theorem prime_oneHundredFiveCY_1128977 : Nat.Prime 1128977 := by norm_num

private theorem prime_oneHundredFiveCY_1243169 : Nat.Prime 1243169 := by norm_num

private theorem prime_oneHundredFiveCY_1256729 : Nat.Prime 1256729 := by norm_num

private theorem prime_oneHundredFiveCY_1376699 : Nat.Prime 1376699 := by norm_num

private theorem prime_oneHundredFiveCY_1423339 : Nat.Prime 1423339 := by norm_num

private theorem prime_oneHundredFiveCY_1429061 : Nat.Prime 1429061 := by norm_num

private theorem prime_oneHundredFiveCY_1524119 : Nat.Prime 1524119 := by norm_num

private theorem prime_oneHundredFiveCY_1736303 : Nat.Prime 1736303 := by norm_num

private theorem prime_oneHundredFiveCY_1768157 : Nat.Prime 1768157 := by norm_num

private theorem prime_oneHundredFiveCY_1822907 : Nat.Prime 1822907 := by norm_num

private theorem prime_oneHundredFiveCY_1861583 : Nat.Prime 1861583 := by norm_num

private theorem prime_oneHundredFiveCY_1868173 : Nat.Prime 1868173 := by norm_num

private theorem prime_oneHundredFiveCY_2011699 : Nat.Prime 2011699 := by norm_num

private theorem prime_oneHundredFiveCY_2115499 : Nat.Prime 2115499 := by norm_num

private theorem prime_oneHundredFiveCY_2155877 : Nat.Prime 2155877 := by norm_num

private theorem prime_oneHundredFiveCY_2325647 : Nat.Prime 2325647 := by norm_num

private theorem prime_oneHundredFiveCY_2433721 : Nat.Prime 2433721 := by norm_num

private theorem prime_oneHundredFiveCY_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredFiveCY_2956061 : Nat.Prime 2956061 := by norm_num

private theorem prime_oneHundredFiveCY_3018307 : Nat.Prime 3018307 := by norm_num

private theorem prime_oneHundredFiveCY_3133331 : Nat.Prime 3133331 := by norm_num

private theorem prime_oneHundredFiveCY_3551813 : Nat.Prime 3551813 := by norm_num

private theorem prime_oneHundredFiveCY_3599009 : Nat.Prime 3599009 := by norm_num

private theorem prime_oneHundredFiveCY_3834907 : Nat.Prime 3834907 := by norm_num

private theorem prime_oneHundredFiveCY_3935629 : Nat.Prime 3935629 := by norm_num

private theorem prime_oneHundredFiveCY_3935887 : Nat.Prime 3935887 := by norm_num

private theorem prime_oneHundredFiveCY_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredFiveCY_4360919 : Nat.Prime 4360919 := by norm_num

private theorem prime_oneHundredFiveCY_4584901 : Nat.Prime 4584901 := by norm_num

private theorem prime_oneHundredFiveCY_4658177 : Nat.Prime 4658177 := by norm_num

private theorem prime_oneHundredFiveCY_4671071 : Nat.Prime 4671071 := by norm_num

private theorem prime_oneHundredFiveCY_4723661 : Nat.Prime 4723661 := by norm_num

private theorem prime_oneHundredFiveCY_4866313 : Nat.Prime 4866313 := by norm_num

private theorem prime_oneHundredFiveCY_4955311 : Nat.Prime 4955311 := by norm_num

private theorem prime_oneHundredFiveCY_4996501 : Nat.Prime 4996501 := by norm_num

private theorem prime_oneHundredFiveCY_5451263 : Nat.Prime 5451263 := by norm_num

private theorem prime_oneHundredFiveCY_5539187 : Nat.Prime 5539187 := by norm_num

private theorem prime_oneHundredFiveCY_6039193 : Nat.Prime 6039193 := by norm_num

private theorem prime_oneHundredFiveCY_6042793 : Nat.Prime 6042793 := by norm_num

private theorem prime_oneHundredFiveCY_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredFiveCY_6333013 : Nat.Prime 6333013 := by norm_num

private theorem prime_oneHundredFiveCY_7015717 : Nat.Prime 7015717 := by norm_num

private theorem prime_oneHundredFiveCY_7583137 : Nat.Prime 7583137 := by norm_num

private theorem prime_oneHundredFiveCY_7964137 : Nat.Prime 7964137 := by norm_num

private theorem prime_oneHundredFiveCY_8095547 : Nat.Prime 8095547 := by norm_num

private theorem prime_oneHundredFiveCY_8387447 : Nat.Prime 8387447 := by norm_num

private theorem prime_oneHundredFiveCY_8828689 : Nat.Prime 8828689 := by norm_num

private theorem prime_oneHundredFiveCY_9319549 : Nat.Prime 9319549 := by norm_num

private theorem prime_oneHundredFiveCY_10517539 : Nat.Prime 10517539 := by norm_num

private theorem prime_oneHundredFiveCY_10713539 : Nat.Prime 10713539 := by norm_num

private theorem prime_oneHundredFiveCY_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiveCY_11104427 : Nat.Prime 11104427 := by norm_num

private theorem prime_oneHundredFiveCY_12250097 : Nat.Prime 12250097 := by norm_num

private theorem prime_oneHundredFiveCY_13551917 : Nat.Prime 13551917 := by norm_num

private theorem prime_oneHundredFiveCY_13617913 : Nat.Prime 13617913 := by norm_num

private theorem prime_oneHundredFiveCY_14265577 : Nat.Prime 14265577 := by norm_num

private theorem prime_oneHundredFiveCY_15863621 : Nat.Prime 15863621 := by norm_num

private theorem prime_oneHundredFiveCY_16727479 : Nat.Prime 16727479 := by norm_num

private theorem prime_oneHundredFiveCY_18262633 : Nat.Prime 18262633 := by norm_num

private theorem prime_oneHundredFiveCY_18556441 : Nat.Prime 18556441 := by norm_num

private theorem prime_oneHundredFiveCY_21099097 : Nat.Prime 21099097 := by norm_num

private theorem prime_oneHundredFiveCY_21433351 : Nat.Prime 21433351 := by norm_num

private theorem prime_oneHundredFiveCY_21947089 : Nat.Prime 21947089 := by norm_num

private theorem prime_oneHundredFiveCY_23064677 : Nat.Prime 23064677 := by norm_num

private theorem prime_oneHundredFiveCY_23964467 : Nat.Prime 23964467 := by norm_num

private theorem prime_oneHundredFiveCY_24689591 : Nat.Prime 24689591 := by norm_num

private theorem prime_oneHundredFiveCY_25863419 : Nat.Prime 25863419 := by norm_num

private theorem prime_oneHundredFiveCY_30150811 : Nat.Prime 30150811 := by
  apply lucas_primality 30150811 (10 : ZMod 30150811)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (335009, 1)] : List FactorBlock).map factorBlockValue).prod) = 30150811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_335009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 30150811) ^ 15075405 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 30150811) ^ 10050270 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 30150811) ^ 6030162 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 30150811) ^ 90 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_31308259 : Nat.Prime 31308259 := by
  apply lucas_primality 31308259 (2 : ZMod 31308259)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (499, 1), (10457, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (499, 1), (10457, 1)] : List FactorBlock).map factorBlockValue).prod) = 31308259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_499
      · exact prime_oneHundredFiveCY_10457
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 31308259) ^ 15654129 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31308259) ^ 10436086 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31308259) ^ 62742 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31308259) ^ 2994 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_31824613 : Nat.Prime 31824613 := by
  apply lucas_primality 31824613 (5 : ZMod 31824613)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (17, 1), (149, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (17, 1), (149, 1), (349, 1)] : List FactorBlock).map factorBlockValue).prod) = 31824613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_149
      · exact prime_oneHundredFiveCY_349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31824613) ^ 15912306 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 10608204 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 1872036 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 213588 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 31824613) ^ 91188 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_31969337 : Nat.Prime 31969337 := by
  apply lucas_primality 31969337 (3 : ZMod 31969337)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) = 31969337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_570881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31969337) ^ 15984668 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 4567048 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 56 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_32105053 : Nat.Prime 32105053 := by
  apply lucas_primality 32105053 (5 : ZMod 32105053)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 1), (42467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 1), (42467, 1)] : List FactorBlock).map factorBlockValue).prod) = 32105053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_42467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 32105053) ^ 16052526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32105053) ^ 10701684 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32105053) ^ 4586436 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 32105053) ^ 756 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_73
      · exact prime_oneHundredFiveCY_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_33117977 : Nat.Prime 33117977 := by
  apply lucas_primality 33117977 (3 : ZMod 33117977)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (179989, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (179989, 1)] : List FactorBlock).map factorBlockValue).prod) = 33117977 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_179989
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 33117977) ^ 16558988 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 33117977) ^ 1439912 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 33117977) ^ 184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_40455817 : Nat.Prime 40455817 := by
  apply lucas_primality 40455817 (5 : ZMod 40455817)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (739, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (739, 1), (2281, 1)] : List FactorBlock).map factorBlockValue).prod) = 40455817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_739
      · exact prime_oneHundredFiveCY_2281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 40455817) ^ 20227908 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40455817) ^ 13485272 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40455817) ^ 54744 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 40455817) ^ 17736 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_43667153 : Nat.Prime 43667153 := by
  apply lucas_primality 43667153 (3 : ZMod 43667153)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (160541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (160541, 1)] : List FactorBlock).map factorBlockValue).prod) = 43667153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_160541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 43667153) ^ 21833576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 43667153) ^ 2568656 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 43667153) ^ 272 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_52864081 : Nat.Prime 52864081 := by
  apply lucas_primality 52864081 (17 : ZMod 52864081)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (19, 1), (11593, 1)] : List FactorBlock).map factorBlockValue).prod) = 52864081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_11593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 52864081) ^ 26432040 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 17621360 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 10572816 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 2782320 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 52864081) ^ 4560 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_53433161 : Nat.Prime 53433161 := by
  apply lucas_primality 53433161 (3 : ZMod 53433161)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (11, 1), (121439, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (11, 1), (121439, 1)] : List FactorBlock).map factorBlockValue).prod) = 53433161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_121439
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 53433161) ^ 26716580 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53433161) ^ 10686632 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53433161) ^ 4857560 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53433161) ^ 440 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_59958013 : Nat.Prime 59958013 := by
  apply lucas_primality 59958013 (2 : ZMod 59958013)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4996501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4996501, 1)] : List FactorBlock).map factorBlockValue).prod) = 59958013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_4996501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59958013) ^ 29979006 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59958013) ^ 19986004 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 59958013) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_64452701 : Nat.Prime 64452701 := by
  apply lucas_primality 64452701 (2 : ZMod 64452701)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (13, 1), (43, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (13, 1), (43, 1), (1153, 1)] : List FactorBlock).map factorBlockValue).prod) = 64452701 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_1153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 64452701) ^ 32226350 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64452701) ^ 12890540 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64452701) ^ 4957900 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64452701) ^ 1498900 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 64452701) ^ 55900 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_64887553 : Nat.Prime 64887553 := by
  apply lucas_primality 64887553 (5 : ZMod 64887553)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 2), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 2), (28163, 1)] : List FactorBlock).map factorBlockValue).prod) = 64887553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_28163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 64887553) ^ 32443776 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 64887553) ^ 21629184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 64887553) ^ 2304 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_66909917 : Nat.Prime 66909917 := by
  apply lucas_primality 66909917 (2 : ZMod 66909917)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66909917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_16727479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66909917) ^ 33454958 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 66909917) ^ 4 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_67012129 : Nat.Prime 67012129 := by
  apply lucas_primality 67012129 (11 : ZMod 67012129)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (232681, 1)] : List FactorBlock).map factorBlockValue).prod) = 67012129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_232681
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 67012129) ^ 33506064 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 67012129) ^ 22337376 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 67012129) ^ 288 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_67902011 : Nat.Prime 67902011 := by
  apply lucas_primality 67902011 (2 : ZMod 67902011)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (19, 1), (53, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (19, 1), (53, 1), (613, 1)] : List FactorBlock).map factorBlockValue).prod) = 67902011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_53
      · exact prime_oneHundredFiveCY_613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 67902011) ^ 33951005 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 13580402 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 6172910 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 3573790 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 1281170 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67902011) ^ 110770 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_72918553 : Nat.Prime 72918553 := by
  apply lucas_primality 72918553 (10 : ZMod 72918553)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (434039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (434039, 1)] : List FactorBlock).map factorBlockValue).prod) = 72918553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_434039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 72918553) ^ 36459276 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 72918553) ^ 24306184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 72918553) ^ 10416936 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 72918553) ^ 168 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_82022119 : Nat.Prime 82022119 := by
  apply lucas_primality 82022119 (6 : ZMod 82022119)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (369469, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (369469, 1)] : List FactorBlock).map factorBlockValue).prod) = 82022119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_369469
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 82022119) ^ 41011059 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82022119) ^ 27340706 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82022119) ^ 2216814 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 82022119) ^ 222 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_84794867 : Nat.Prime 84794867 := by
  apply lucas_primality 84794867 (2 : ZMod 84794867)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (1049, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (1049, 1), (3109, 1)] : List FactorBlock).map factorBlockValue).prod) = 84794867 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_1049
      · exact prime_oneHundredFiveCY_3109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84794867) ^ 42397433 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84794867) ^ 6522682 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84794867) ^ 80834 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 84794867) ^ 27274 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_88812211 : Nat.Prime 88812211 := by
  apply lucas_primality 88812211 (3 : ZMod 88812211)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (29, 1), (31, 1), (37, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 88812211 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_89
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88812211) ^ 44406105 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 29604070 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 17762442 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 3062490 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2864910 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 2400330 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 88812211) ^ 997890 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_89151479 : Nat.Prime 89151479 := by
  apply lucas_primality 89151479 (7 : ZMod 89151479)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (59, 1), (89, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (59, 1), (89, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 89151479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_59
      · exact prime_oneHundredFiveCY_89
      · exact prime_oneHundredFiveCY_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 89151479) ^ 44575739 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 89151479) ^ 6857806 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 89151479) ^ 1511042 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 89151479) ^ 1001702 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 89151479) ^ 136526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_89710769 : Nat.Prime 89710769 := by
  apply lucas_primality 89710769 (3 : ZMod 89710769)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 2), (17, 1), (53, 1), (127, 1)] : List FactorBlock).map factorBlockValue).prod) = 89710769 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_53
      · exact prime_oneHundredFiveCY_127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 89710769) ^ 44855384 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 12815824 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 5277104 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 1692656 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 89710769) ^ 706384 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_95181727 : Nat.Prime 95181727 := by
  apply lucas_primality 95181727 (3 : ZMod 95181727)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (15863621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (15863621, 1)] : List FactorBlock).map factorBlockValue).prod) = 95181727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_15863621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 95181727) ^ 47590863 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95181727) ^ 31727242 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 95181727) ^ 6 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_110796689 : Nat.Prime 110796689 := by
  apply lucas_primality 110796689 (3 : ZMod 110796689)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (103, 1), (67231, 1)] : List FactorBlock).map factorBlockValue).prod) = 110796689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_103
      · exact prime_oneHundredFiveCY_67231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 110796689) ^ 55398344 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1075696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 110796689) ^ 1648 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_125233037 : Nat.Prime 125233037 := by
  apply lucas_primality 125233037 (2 : ZMod 125233037)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (31308259, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (31308259, 1)] : List FactorBlock).map factorBlockValue).prod) = 125233037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_31308259
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 125233037) ^ 62616518 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 125233037) ^ 4 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_136631401 : Nat.Prime 136631401 := by
  apply lucas_primality 136631401 (31 : ZMod 136631401)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 2), (227719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 2), (227719, 1)] : List FactorBlock).map factorBlockValue).prod) = 136631401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_227719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (31 : ZMod 136631401) ^ 68315700 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 136631401) ^ 45543800 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 136631401) ^ 27326280 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 136631401) ^ 600 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_148525189 : Nat.Prime 148525189 := by
  apply lucas_primality 148525189 (2 : ZMod 148525189)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1768157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1768157, 1)] : List FactorBlock).map factorBlockValue).prod) = 148525189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_1768157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 148525189) ^ 74262594 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148525189) ^ 49508396 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148525189) ^ 21217884 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148525189) ^ 84 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_153124189 : Nat.Prime 153124189 := by
  apply lucas_primality 153124189 (2 : ZMod 153124189)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1822907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1822907, 1)] : List FactorBlock).map factorBlockValue).prod) = 153124189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_1822907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 153124189) ^ 76562094 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153124189) ^ 51041396 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153124189) ^ 21874884 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 153124189) ^ 84 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_155052727 : Nat.Prime 155052727 := by
  apply lucas_primality 155052727 (3 : ZMod 155052727)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (193, 1), (257, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (193, 1), (257, 1), (521, 1)] : List FactorBlock).map factorBlockValue).prod) = 155052727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_193
      · exact prime_oneHundredFiveCY_257
      · exact prime_oneHundredFiveCY_521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 155052727) ^ 77526363 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 155052727) ^ 51684242 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 155052727) ^ 803382 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 155052727) ^ 603318 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 155052727) ^ 297606 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_160346779 : Nat.Prime 160346779 := by
  apply lucas_primality 160346779 (2 : ZMod 160346779)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59, 1), (452957, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59, 1), (452957, 1)] : List FactorBlock).map factorBlockValue).prod) = 160346779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_59
      · exact prime_oneHundredFiveCY_452957
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 160346779) ^ 80173389 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 160346779) ^ 53448926 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 160346779) ^ 2717742 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 160346779) ^ 354 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_173131403 : Nat.Prime 173131403 := by
  apply lucas_primality 173131403 (2 : ZMod 173131403)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (223, 1), (388187, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (223, 1), (388187, 1)] : List FactorBlock).map factorBlockValue).prod) = 173131403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_223
      · exact prime_oneHundredFiveCY_388187
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173131403) ^ 86565701 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 173131403) ^ 776374 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 173131403) ^ 446 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_175187269 : Nat.Prime 175187269 := by
  apply lucas_primality 175187269 (7 : ZMod 175187269)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4866313, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4866313, 1)] : List FactorBlock).map factorBlockValue).prod) = 175187269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_4866313
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 175187269) ^ 87593634 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 175187269) ^ 58395756 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 175187269) ^ 36 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_183832669 : Nat.Prime 183832669 := by
  apply lucas_primality 183832669 (2 : ZMod 183832669)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1447, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1447, 1), (3529, 1)] : List FactorBlock).map factorBlockValue).prod) = 183832669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1447
      · exact prime_oneHundredFiveCY_3529
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 183832669) ^ 91916334 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 61277556 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 127044 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 183832669) ^ 52092 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_185564411 : Nat.Prime 185564411 := by
  apply lucas_primality 185564411 (2 : ZMod 185564411)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (18556441, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (18556441, 1)] : List FactorBlock).map factorBlockValue).prod) = 185564411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_18556441
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 185564411) ^ 92782205 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 185564411) ^ 37112882 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 185564411) ^ 10 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_222099587 : Nat.Prime 222099587 := by
  apply lucas_primality 222099587 (2 : ZMod 222099587)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (571, 1), (194483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (571, 1), (194483, 1)] : List FactorBlock).map factorBlockValue).prod) = 222099587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_571
      · exact prime_oneHundredFiveCY_194483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 222099587) ^ 111049793 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 222099587) ^ 388966 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 222099587) ^ 1142 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_248048113 : Nat.Prime 248048113 := by
  apply lucas_primality 248048113 (7 : ZMod 248048113)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (13, 1), (31, 1), (12823, 1)] : List FactorBlock).map factorBlockValue).prod) = 248048113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_12823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 248048113) ^ 124024056 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 82682704 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19080624 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 8001552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 248048113) ^ 19344 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_258876179 : Nat.Prime 258876179 := by
  apply lucas_primality 258876179 (2 : ZMod 258876179)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (23, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (23, 1), (26927, 1)] : List FactorBlock).map factorBlockValue).prod) = 258876179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_26927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 258876179) ^ 129438089 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 258876179) ^ 23534198 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 258876179) ^ 13625062 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 258876179) ^ 11255486 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 258876179) ^ 9614 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_265986547 : Nat.Prime 265986547 := by
  apply lucas_primality 265986547 (7 : ZMod 265986547)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (6333013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (6333013, 1)] : List FactorBlock).map factorBlockValue).prod) = 265986547 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_6333013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 265986547) ^ 132993273 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 265986547) ^ 88662182 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 265986547) ^ 37998078 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 265986547) ^ 42 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_278993839 : Nat.Prime 278993839 := by
  apply lucas_primality 278993839 (3 : ZMod 278993839)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) = 278993839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_1256729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 278993839) ^ 139496919 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 92997946 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 7540374 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 222 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_292202129 : Nat.Prime 292202129 := by
  apply lucas_primality 292202129 (3 : ZMod 292202129)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) = 292202129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_18262633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 292202129) ^ 146101064 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 292202129) ^ 16 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_350415259 : Nat.Prime 350415259 := by
  apply lucas_primality 350415259 (2 : ZMod 350415259)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (31, 1), (101, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (31, 1), (101, 1), (811, 1)] : List FactorBlock).map factorBlockValue).prod) = 350415259 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_101
      · exact prime_oneHundredFiveCY_811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 350415259) ^ 175207629 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 350415259) ^ 116805086 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 350415259) ^ 15235446 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 350415259) ^ 11303718 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 350415259) ^ 3469458 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 350415259) ^ 432078 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_351518777 : Nat.Prime 351518777 := by
  apply lucas_primality 351518777 (3 : ZMod 351518777)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (1319, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (1319, 1), (4759, 1)] : List FactorBlock).map factorBlockValue).prod) = 351518777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_1319
      · exact prime_oneHundredFiveCY_4759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 351518777) ^ 175759388 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 50216968 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 266504 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 351518777) ^ 73864 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_354122287 : Nat.Prime 354122287 := by
  apply lucas_primality 354122287 (3 : ZMod 354122287)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (196081, 1)] : List FactorBlock).map factorBlockValue).prod) = 354122287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_196081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 354122287) ^ 177061143 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 118040762 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 50588898 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 8235402 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 354122287) ^ 1806 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_362051087 : Nat.Prime 362051087 := by
  apply lucas_primality 362051087 (5 : ZMod 362051087)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12539, 1), (14437, 1)] : List FactorBlock).map factorBlockValue).prod) = 362051087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_12539
      · exact prime_oneHundredFiveCY_14437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 362051087) ^ 181025543 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 28874 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 362051087) ^ 25078 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_380726909 : Nat.Prime 380726909 := by
  apply lucas_primality 380726909 (2 : ZMod 380726909)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (95181727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (95181727, 1)] : List FactorBlock).map factorBlockValue).prod) = 380726909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_95181727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 380726909) ^ 190363454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 380726909) ^ 4 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_427967311 : Nat.Prime 427967311 := by
  apply lucas_primality 427967311 (7 : ZMod 427967311)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (14265577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (14265577, 1)] : List FactorBlock).map factorBlockValue).prod) = 427967311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_14265577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 427967311) ^ 213983655 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 142655770 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 85593462 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 427967311) ^ 30 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_545363909 : Nat.Prime 545363909 := by
  apply lucas_primality 545363909 (2 : ZMod 545363909)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (127, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (127, 1), (37019, 1)] : List FactorBlock).map factorBlockValue).prod) = 545363909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_127
      · exact prime_oneHundredFiveCY_37019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 545363909) ^ 272681954 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 18805652 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 4294204 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 545363909) ^ 14732 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_596250997 : Nat.Prime 596250997 := by
  apply lucas_primality 596250997 (5 : ZMod 596250997)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (265709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (265709, 1)] : List FactorBlock).map factorBlockValue).prod) = 596250997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_265709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 596250997) ^ 298125498 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 198750332 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 54204636 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 35073588 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 2244 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_627983903 : Nat.Prime 627983903 := by
  apply lucas_primality 627983903 (7 : ZMod 627983903)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (199, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (199, 1), (2477, 1)] : List FactorBlock).map factorBlockValue).prod) = 627983903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_199
      · exact prime_oneHundredFiveCY_2477
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 627983903) ^ 313991951 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 627983903) ^ 89711986 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 627983903) ^ 48306454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 627983903) ^ 3155698 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 627983903) ^ 253526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_630418703 : Nat.Prime 630418703 := by
  apply lucas_primality 630418703 (5 : ZMod 630418703)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (149, 1), (2115499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (149, 1), (2115499, 1)] : List FactorBlock).map factorBlockValue).prod) = 630418703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_149
      · exact prime_oneHundredFiveCY_2115499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 630418703) ^ 315209351 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 630418703) ^ 4230998 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 630418703) ^ 298 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_635013539 : Nat.Prime 635013539 := by
  apply lucas_primality 635013539 (2 : ZMod 635013539)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (67, 1), (77687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (67, 1), (77687, 1)] : List FactorBlock).map factorBlockValue).prod) = 635013539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_67
      · exact prime_oneHundredFiveCY_77687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 635013539) ^ 317506769 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 635013539) ^ 10410058 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 635013539) ^ 9477814 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 635013539) ^ 8174 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17203
      · exact prime_oneHundredFiveCY_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_101
      · exact prime_oneHundredFiveCY_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_759567493 : Nat.Prime 759567493 := by
  apply lucas_primality 759567493 (5 : ZMod 759567493)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21099097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21099097, 1)] : List FactorBlock).map factorBlockValue).prod) = 759567493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_21099097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 759567493) ^ 379783746 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 759567493) ^ 253189164 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 759567493) ^ 36 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_777122653 : Nat.Prime 777122653 := by
  apply lucas_primality 777122653 (7 : ZMod 777122653)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (127, 1), (419, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (127, 1), (419, 1), (1217, 1)] : List FactorBlock).map factorBlockValue).prod) = 777122653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_127
      · exact prime_oneHundredFiveCY_419
      · exact prime_oneHundredFiveCY_1217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 777122653) ^ 388561326 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 259040884 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 6119076 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 1854708 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 777122653) ^ 638556 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_819788407 : Nat.Prime 819788407 := by
  apply lucas_primality 819788407 (5 : ZMod 819788407)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (136631401, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (136631401, 1)] : List FactorBlock).map factorBlockValue).prod) = 819788407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_136631401
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 819788407) ^ 409894203 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 819788407) ^ 273262802 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 819788407) ^ 6 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1101126877 : Nat.Prime 1101126877 := by
  apply lucas_primality 1101126877 (2 : ZMod 1101126877)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101126877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_457
      · exact prime_oneHundredFiveCY_200789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1101126877) ^ 550563438 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 367042292 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 2409468 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 5484 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1133535457 : Nat.Prime 1133535457 := by
  apply lucas_primality 1133535457 (5 : ZMod 1133535457)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (3935887, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (3935887, 1)] : List FactorBlock).map factorBlockValue).prod) = 1133535457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_3935887
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1133535457) ^ 566767728 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1133535457) ^ 377845152 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1133535457) ^ 288 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1143177577 : Nat.Prime 1143177577 := by
  apply lucas_primality 1143177577 (5 : ZMod 1143177577)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (31, 1), (61, 1), (25189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1143177577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_25189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1143177577) ^ 571588788 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 381059192 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 36876696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 18740616 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1143177577) ^ 45384 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1238109149 : Nat.Prime 1238109149 := by
  apply lucas_primality 1238109149 (2 : ZMod 1238109149)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (43, 1), (359, 1), (20051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (43, 1), (359, 1), (20051, 1)] : List FactorBlock).map factorBlockValue).prod) = 1238109149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_359
      · exact prime_oneHundredFiveCY_20051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1238109149) ^ 619054574 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238109149) ^ 28793236 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238109149) ^ 3448772 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1238109149) ^ 61748 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1255967807 : Nat.Prime 1255967807 := by
  apply lucas_primality 1255967807 (5 : ZMod 1255967807)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (627983903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (627983903, 1)] : List FactorBlock).map factorBlockValue).prod) = 1255967807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_627983903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1255967807) ^ 627983903 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1255967807) ^ 2 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1256493827 : Nat.Prime 1256493827 := by
  apply lucas_primality 1256493827 (2 : ZMod 1256493827)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (4723661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (4723661, 1)] : List FactorBlock).map factorBlockValue).prod) = 1256493827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_4723661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1256493827) ^ 628246913 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256493827) ^ 179499118 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256493827) ^ 66131254 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1256493827) ^ 266 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1389262187 : Nat.Prime 1389262187 := by
  apply lucas_primality 1389262187 (2 : ZMod 1389262187)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (53433161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (53433161, 1)] : List FactorBlock).map factorBlockValue).prod) = 1389262187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_53433161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1389262187) ^ 694631093 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1389262187) ^ 106866322 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1389262187) ^ 26 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1643753773 : Nat.Prime 1643753773 := by
  apply lucas_primality 1643753773 (2 : ZMod 1643753773)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (1597, 1), (28591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (1597, 1), (28591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1643753773 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1597
      · exact prime_oneHundredFiveCY_28591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1643753773) ^ 821876886 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1643753773) ^ 547917924 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1643753773) ^ 1029276 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1643753773) ^ 57492 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1751872691 : Nat.Prime 1751872691 := by
  apply lucas_primality 1751872691 (6 : ZMod 1751872691)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (175187269, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (175187269, 1)] : List FactorBlock).map factorBlockValue).prod) = 1751872691 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_175187269
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 1751872691) ^ 875936345 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1751872691) ^ 350374538 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 1751872691) ^ 10 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1785955307 : Nat.Prime 1785955307 := by
  apply lucas_primality 1785955307 (2 : ZMod 1785955307)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (8839, 1), (101027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (8839, 1), (101027, 1)] : List FactorBlock).map factorBlockValue).prod) = 1785955307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_8839
      · exact prime_oneHundredFiveCY_101027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1785955307) ^ 892977653 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785955307) ^ 202054 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1785955307) ^ 17678 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1861975811 : Nat.Prime 1861975811 := by
  apply lucas_primality 1861975811 (2 : ZMod 1861975811)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (8095547, 1)] : List FactorBlock).map factorBlockValue).prod) = 1861975811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_8095547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1861975811) ^ 930987905 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 372395162 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 80955470 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1861975811) ^ 230 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1900536217 : Nat.Prime 1900536217 := by
  apply lucas_primality 1900536217 (5 : ZMod 1900536217)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (4658177, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (4658177, 1)] : List FactorBlock).map factorBlockValue).prod) = 1900536217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_4658177
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1900536217) ^ 950268108 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1900536217) ^ 633512072 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1900536217) ^ 111796248 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1900536217) ^ 408 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2016230959 : Nat.Prime 2016230959 := by
  apply lucas_primality 2016230959 (3 : ZMod 2016230959)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016230959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_229
      · exact prime_oneHundredFiveCY_69877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2016230959) ^ 1008115479 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 672076986 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 288032994 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 8804502 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 28854 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2212469803 : Nat.Prime 2212469803 := by
  apply lucas_primality 2212469803 (2 : ZMod 2212469803)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (505823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (505823, 1)] : List FactorBlock).map factorBlockValue).prod) = 2212469803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_505823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2212469803) ^ 1106234901 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2212469803) ^ 737489934 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2212469803) ^ 4374 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2503484351 : Nat.Prime 2503484351 := by
  apply lucas_primality 2503484351 (19 : ZMod 2503484351)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (107, 1), (467941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (107, 1), (467941, 1)] : List FactorBlock).map factorBlockValue).prod) = 2503484351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_107
      · exact prime_oneHundredFiveCY_467941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 2503484351) ^ 1251742175 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 500696870 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 23397050 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 2503484351) ^ 5350 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2854259137 : Nat.Prime 2854259137 := by
  apply lucas_primality 2854259137 (5 : ZMod 2854259137)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 2), (4955311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 2), (4955311, 1)] : List FactorBlock).map factorBlockValue).prod) = 2854259137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_4955311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2854259137) ^ 1427129568 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2854259137) ^ 951419712 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2854259137) ^ 576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4158705293 : Nat.Prime 4158705293 := by
  apply lucas_primality 4158705293 (2 : ZMod 4158705293)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (148525189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (148525189, 1)] : List FactorBlock).map factorBlockValue).prod) = 4158705293 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_148525189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4158705293) ^ 2079352646 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4158705293) ^ 594100756 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4158705293) ^ 28 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4568722909 : Nat.Prime 4568722909 := by
  apply lucas_primality 4568722909 (6 : ZMod 4568722909)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (380726909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (380726909, 1)] : List FactorBlock).map factorBlockValue).prod) = 4568722909 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_380726909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 4568722909) ^ 2284361454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4568722909) ^ 1522907636 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4568722909) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_6011423573 : Nat.Prime 6011423573 := by
  apply lucas_primality 6011423573 (2 : ZMod 6011423573)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (11, 1), (29, 1), (293, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (11, 1), (29, 1), (293, 1), (2297, 1)] : List FactorBlock).map factorBlockValue).prod) = 6011423573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_293
      · exact prime_oneHundredFiveCY_2297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6011423573) ^ 3005711786 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6011423573) ^ 858774796 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6011423573) ^ 546493052 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6011423573) ^ 207290468 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6011423573) ^ 20516804 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6011423573) ^ 2617076 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_311
      · exact prime_oneHundredFiveCY_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_7549237799 : Nat.Prime 7549237799 := by
  apply lucas_primality 7549237799 (11 : ZMod 7549237799)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (1117, 1), (91331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (1117, 1), (91331, 1)] : List FactorBlock).map factorBlockValue).prod) = 7549237799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_1117
      · exact prime_oneHundredFiveCY_91331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 7549237799) ^ 3774618899 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 7549237799) ^ 204033454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 7549237799) ^ 6758494 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 7549237799) ^ 82658 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_9926795467 : Nat.Prime 9926795467 := by
  apply lucas_primality 9926795467 (2 : ZMod 9926795467)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (5231, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (5231, 1), (15061, 1)] : List FactorBlock).map factorBlockValue).prod) = 9926795467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_5231
      · exact prime_oneHundredFiveCY_15061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9926795467) ^ 4963397733 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926795467) ^ 3308931822 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926795467) ^ 1418113638 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926795467) ^ 1897686 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926795467) ^ 659106 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_11129533489 : Nat.Prime 11129533489 := by
  apply lucas_primality 11129533489 (11 : ZMod 11129533489)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 4), (653, 1), (13151, 1)] : List FactorBlock).map factorBlockValue).prod) = 11129533489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_653
      · exact prime_oneHundredFiveCY_13151
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 11129533489) ^ 5564766744 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 3709844496 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 17043696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 11129533489) ^ 846288 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_16754650799 : Nat.Prime 16754650799 := by
  apply lucas_primality 16754650799 (19 : ZMod 16754650799)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (113, 1), (4360919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (113, 1), (4360919, 1)] : List FactorBlock).map factorBlockValue).prod) = 16754650799 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_113
      · exact prime_oneHundredFiveCY_4360919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (19 : ZMod 16754650799) ^ 8377325399 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 16754650799) ^ 985567694 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 16754650799) ^ 148271246 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (19 : ZMod 16754650799) ^ 3842 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_17974328653 : Nat.Prime 17974328653 := by
  apply lucas_primality 17974328653 (2 : ZMod 17974328653)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (7, 1), (2131, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (7, 1), (2131, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) = 17974328653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_2131
      · exact prime_oneHundredFiveCY_3719
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 17974328653) ^ 8987164326 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17974328653) ^ 5991442884 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17974328653) ^ 2567761236 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17974328653) ^ 8434692 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17974328653) ^ 4833108 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_20288258719 : Nat.Prime 20288258719 := by
  apply lucas_primality 20288258719 (3 : ZMod 20288258719)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) = 20288258719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_461
      · exact prime_oneHundredFiveCY_80603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20288258719) ^ 10144129359 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 6762752906 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 2898322674 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 1560635286 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 44009238 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 251706 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_24570248051 : Nat.Prime 24570248051 := by
  apply lucas_primality 24570248051 (10 : ZMod 24570248051)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) = 24570248051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_25863419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 24570248051) ^ 12285124025 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 4914049610 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 1293170950 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 950 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_24740943389 : Nat.Prime 24740943389 := by
  apply lucas_primality 24740943389 (2 : ZMod 24740943389)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 2), (31, 1), (109, 1), (37357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 2), (31, 1), (109, 1), (37357, 1)] : List FactorBlock).map factorBlockValue).prod) = 24740943389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_109
      · exact prime_oneHundredFiveCY_37357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 24740943389) ^ 12370471694 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 3534420484 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 798094948 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 226981132 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24740943389) ^ 662284 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_26481235453 : Nat.Prime 26481235453 := by
  apply lucas_primality 26481235453 (6 : ZMod 26481235453)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (1531, 1), (205913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (1531, 1), (205913, 1)] : List FactorBlock).map factorBlockValue).prod) = 26481235453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_1531
      · exact prime_oneHundredFiveCY_205913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26481235453) ^ 13240617726 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 26481235453) ^ 8827078484 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 26481235453) ^ 3783033636 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 26481235453) ^ 17296692 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 26481235453) ^ 128604 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_26549637637 : Nat.Prime 26549637637 := by
  apply lucas_primality 26549637637 (2 : ZMod 26549637637)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2212469803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2212469803, 1)] : List FactorBlock).map factorBlockValue).prod) = 26549637637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_2212469803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 26549637637) ^ 13274818818 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26549637637) ^ 8849879212 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26549637637) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_26752207429 : Nat.Prime 26752207429 := by
  apply lucas_primality 26752207429 (2 : ZMod 26752207429)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (4621, 1), (160813, 1)] : List FactorBlock).map factorBlockValue).prod) = 26752207429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_4621
      · exact prime_oneHundredFiveCY_160813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 26752207429) ^ 13376103714 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 8917402476 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 5789268 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 26752207429) ^ 166356 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_34454987579 : Nat.Prime 34454987579 := by
  apply lucas_primality 34454987579 (2 : ZMod 34454987579)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (2617, 1), (598447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (2617, 1), (598447, 1)] : List FactorBlock).map factorBlockValue).prod) = 34454987579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_2617
      · exact prime_oneHundredFiveCY_598447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 34454987579) ^ 17227493789 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 34454987579) ^ 3132271598 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 34454987579) ^ 13165834 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 34454987579) ^ 57574 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_44868075229 : Nat.Prime 44868075229 := by
  apply lucas_primality 44868075229 (2 : ZMod 44868075229)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (173, 1), (587, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (173, 1), (587, 1), (4091, 1)] : List FactorBlock).map factorBlockValue).prod) = 44868075229 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_173
      · exact prime_oneHundredFiveCY_587
      · exact prime_oneHundredFiveCY_4091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44868075229) ^ 22434037614 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 14956025076 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 259353036 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 76436244 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 44868075229) ^ 10967508 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_52586168543 : Nat.Prime 52586168543 := by
  apply lucas_primality 52586168543 (5 : ZMod 52586168543)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (1143177577, 1)] : List FactorBlock).map factorBlockValue).prod) = 52586168543 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_1143177577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 52586168543) ^ 26293084271 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 2286355154 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52586168543) ^ 46 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_58221874103 : Nat.Prime 58221874103 := by
  apply lucas_primality 58221874103 (7 : ZMod 58221874103)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4158705293, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4158705293, 1)] : List FactorBlock).map factorBlockValue).prod) = 58221874103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_4158705293
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 58221874103) ^ 29110937051 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 58221874103) ^ 8317410586 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 58221874103) ^ 14 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_67283234531 : Nat.Prime 67283234531 := by
  apply lucas_primality 67283234531 (2 : ZMod 67283234531)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (354122287, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (354122287, 1)] : List FactorBlock).map factorBlockValue).prod) = 67283234531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_354122287
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 67283234531) ^ 33641617265 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 13456646906 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 3541222870 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 67283234531) ^ 190 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_79031450033 : Nat.Prime 79031450033 := by
  apply lucas_primality 79031450033 (3 : ZMod 79031450033)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (37, 2), (1051, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (37, 2), (1051, 1), (3433, 1)] : List FactorBlock).map factorBlockValue).prod) = 79031450033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_1051
      · exact prime_oneHundredFiveCY_3433
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 79031450033) ^ 39515725016 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031450033) ^ 2135985136 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031450033) ^ 75196432 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 79031450033) ^ 23021104 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_101438759971 : Nat.Prime 101438759971 := by
  apply lucas_primality 101438759971 (2 : ZMod 101438759971)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (125233037, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (125233037, 1)] : List FactorBlock).map factorBlockValue).prod) = 101438759971 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_125233037
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 101438759971) ^ 50719379985 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 101438759971) ^ 33812919990 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 101438759971) ^ 20287751994 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 101438759971) ^ 810 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_119846578273 : Nat.Prime 119846578273 := by
  apply lucas_primality 119846578273 (5 : ZMod 119846578273)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (719, 1), (1736303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (719, 1), (1736303, 1)] : List FactorBlock).map factorBlockValue).prod) = 119846578273 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_719
      · exact prime_oneHundredFiveCY_1736303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 119846578273) ^ 59923289136 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 119846578273) ^ 39948859424 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 119846578273) ^ 166685088 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 119846578273) ^ 69024 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_120055286693 : Nat.Prime 120055286693 := by
  apply lucas_primality 120055286693 (2 : ZMod 120055286693)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 2), (248048113, 1)] : List FactorBlock).map factorBlockValue).prod) = 120055286693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_248048113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 120055286693) ^ 60027643346 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 10914116972 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 120055286693) ^ 484 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_140168308879 : Nat.Prime 140168308879 := by
  apply lucas_primality 140168308879 (3 : ZMod 140168308879)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (853, 1), (702239, 1)] : List FactorBlock).map factorBlockValue).prod) = 140168308879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_853
      · exact prime_oneHundredFiveCY_702239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 140168308879) ^ 70084154439 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 46722769626 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 10782177606 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 164323926 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 140168308879) ^ 199602 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_151576875913 : Nat.Prime 151576875913 := by
  apply lucas_primality 151576875913 (5 : ZMod 151576875913)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (82022119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (82022119, 1)] : List FactorBlock).map factorBlockValue).prod) = 151576875913 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_82022119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 151576875913) ^ 75788437956 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 151576875913) ^ 50525625304 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 151576875913) ^ 21653839416 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 151576875913) ^ 13779715992 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 151576875913) ^ 1848 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_89
      · exact prime_oneHundredFiveCY_373
      · exact prime_oneHundredFiveCY_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_183987037393 : Nat.Prime 183987037393 := by
  apply lucas_primality 183987037393 (7 : ZMod 183987037393)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (457, 1), (8387447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (457, 1), (8387447, 1)] : List FactorBlock).map factorBlockValue).prod) = 183987037393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_457
      · exact prime_oneHundredFiveCY_8387447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 183987037393) ^ 91993518696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 183987037393) ^ 61329012464 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 183987037393) ^ 402597456 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 183987037393) ^ 21936 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_184851497767 : Nat.Prime 184851497767 := by
  apply lucas_primality 184851497767 (6 : ZMod 184851497767)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (23, 1), (431, 1), (239069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (23, 1), (431, 1), (239069, 1)] : List FactorBlock).map factorBlockValue).prod) = 184851497767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_431
      · exact prime_oneHundredFiveCY_239069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 184851497767) ^ 92425748883 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 184851497767) ^ 61617165922 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 184851497767) ^ 14219345982 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 184851497767) ^ 8037021642 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 184851497767) ^ 428889786 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 184851497767) ^ 773214 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_218280729577 : Nat.Prime 218280729577 := by
  apply lucas_primality 218280729577 (10 : ZMod 218280729577)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (13, 1), (61, 1), (197, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (13, 1), (61, 1), (197, 1), (8317, 1)] : List FactorBlock).map factorBlockValue).prod) = 218280729577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_197
      · exact prime_oneHundredFiveCY_8317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 218280729577) ^ 109140364788 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 72760243192 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 31182961368 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 16790825352 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 3578372616 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 1108024008 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 218280729577) ^ 26245128 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_222133410637 : Nat.Prime 222133410637 := by
  apply lucas_primality 222133410637 (5 : ZMod 222133410637)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (373, 1), (3449, 1), (14389, 1)] : List FactorBlock).map factorBlockValue).prod) = 222133410637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_373
      · exact prime_oneHundredFiveCY_3449
      · exact prime_oneHundredFiveCY_14389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 222133410637) ^ 111066705318 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 74044470212 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 595531932 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 64405164 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 222133410637) ^ 15437724 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_229483735993 : Nat.Prime 229483735993 := by
  apply lucas_primality 229483735993 (11 : ZMod 229483735993)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (7, 1), (19, 1), (23964467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (7, 1), (19, 1), (23964467, 1)] : List FactorBlock).map factorBlockValue).prod) = 229483735993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_23964467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 229483735993) ^ 114741867996 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 229483735993) ^ 76494578664 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 229483735993) ^ 32783390856 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 229483735993) ^ 12078091368 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 229483735993) ^ 9576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_235295344231 : Nat.Prime 235295344231 := by
  apply lucas_primality 235295344231 (3 : ZMod 235295344231)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (50341, 1), (155801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (50341, 1), (155801, 1)] : List FactorBlock).map factorBlockValue).prod) = 235295344231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_50341
      · exact prime_oneHundredFiveCY_155801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 235295344231) ^ 117647672115 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 235295344231) ^ 78431781410 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 235295344231) ^ 47059068846 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 235295344231) ^ 4674030 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 235295344231) ^ 1510230 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_247535343961 : Nat.Prime 247535343961 := by
  apply lucas_primality 247535343961 (7 : ZMod 247535343961)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (22541, 1), (91513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (22541, 1), (91513, 1)] : List FactorBlock).map factorBlockValue).prod) = 247535343961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_22541
      · exact prime_oneHundredFiveCY_91513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 247535343961) ^ 123767671980 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 247535343961) ^ 82511781320 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 247535343961) ^ 49507068792 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 247535343961) ^ 10981560 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 247535343961) ^ 2704920 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_251174804057 : Nat.Prime 251174804057 := by
  apply lucas_primality 251174804057 (3 : ZMod 251174804057)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2854259137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2854259137, 1)] : List FactorBlock).map factorBlockValue).prod) = 251174804057 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_2854259137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 251174804057) ^ 125587402028 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 251174804057) ^ 22834073096 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 251174804057) ^ 88 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_273677215249 : Nat.Prime 273677215249 := by
  apply lucas_primality 273677215249 (31 : ZMod 273677215249)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (1900536217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (1900536217, 1)] : List FactorBlock).map factorBlockValue).prod) = 273677215249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1900536217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (31 : ZMod 273677215249) ^ 136838607624 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 273677215249) ^ 91225738416 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 273677215249) ^ 144 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_317774825437 : Nat.Prime 317774825437 := by
  apply lucas_primality 317774825437 (2 : ZMod 317774825437)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (26481235453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (26481235453, 1)] : List FactorBlock).map factorBlockValue).prod) = 317774825437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_26481235453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 317774825437) ^ 158887412718 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 317774825437) ^ 105924941812 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 317774825437) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_3931
      · exact prime_oneHundredFiveCY_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_402995739827 : Nat.Prime 402995739827 := by
  apply lucas_primality 402995739827 (2 : ZMod 402995739827)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (41, 1), (163, 1), (30150811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (41, 1), (163, 1), (30150811, 1)] : List FactorBlock).map factorBlockValue).prod) = 402995739827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_41
      · exact prime_oneHundredFiveCY_163
      · exact prime_oneHundredFiveCY_30150811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 402995739827) ^ 201497869913 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 402995739827) ^ 9829164386 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 402995739827) ^ 2472366502 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 402995739827) ^ 13366 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_625819384877 : Nat.Prime 625819384877 := by
  apply lucas_primality 625819384877 (2 : ZMod 625819384877)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (41, 1), (383, 1), (1423339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (41, 1), (383, 1), (1423339, 1)] : List FactorBlock).map factorBlockValue).prod) = 625819384877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_41
      · exact prime_oneHundredFiveCY_383
      · exact prime_oneHundredFiveCY_1423339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625819384877) ^ 312909692438 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 625819384877) ^ 89402769268 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 625819384877) ^ 15263887436 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 625819384877) ^ 1633993172 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 625819384877) ^ 439684 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_625830854527 : Nat.Prime 625830854527 := by
  apply lucas_primality 625830854527 (3 : ZMod 625830854527)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (17, 1), (29, 1), (431, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (17, 1), (29, 1), (431, 1), (18181, 1)] : List FactorBlock).map factorBlockValue).prod) = 625830854527 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_431
      · exact prime_oneHundredFiveCY_18181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 625830854527) ^ 312915427263 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 208610284842 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 36813579678 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 21580374294 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 1452043746 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 625830854527) ^ 34422246 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_649654378099 : Nat.Prime 649654378099 := by
  apply lucas_primality 649654378099 (10 : ZMod 649654378099)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23, 1), (427967311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23, 1), (427967311, 1)] : List FactorBlock).map factorBlockValue).prod) = 649654378099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_427967311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 649654378099) ^ 324827189049 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 216551459366 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 59059488918 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 28245842526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 649654378099) ^ 1518 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_674756143339 : Nat.Prime 674756143339 := by
  apply lucas_primality 674756143339 (3 : ZMod 674756143339)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) = 674756143339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_67
      · exact prime_oneHundredFiveCY_313
      · exact prime_oneHundredFiveCY_80039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 674756143339) ^ 337378071669 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 224918714446 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 10070987214 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 2155770426 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 8430342 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_691788953137 : Nat.Prime 691788953137 := by
  apply lucas_primality 691788953137 (10 : ZMod 691788953137)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (41, 1), (351518777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (41, 1), (351518777, 1)] : List FactorBlock).map factorBlockValue).prod) = 691788953137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_41
      · exact prime_oneHundredFiveCY_351518777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 691788953137) ^ 345894476568 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 230596317712 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 16872901296 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 691788953137) ^ 1968 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_806182978687 : Nat.Prime 806182978687 := by
  apply lucas_primality 806182978687 (3 : ZMod 806182978687)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (181, 1), (43667153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (181, 1), (43667153, 1)] : List FactorBlock).map factorBlockValue).prod) = 806182978687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_181
      · exact prime_oneHundredFiveCY_43667153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 806182978687) ^ 403091489343 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 806182978687) ^ 268727659562 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 806182978687) ^ 47422528158 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 806182978687) ^ 4454049606 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 806182978687) ^ 18462 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_947678621413 : Nat.Prime 947678621413 := by
  apply lucas_primality 947678621413 (2 : ZMod 947678621413)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (14591, 1), (80783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (14591, 1), (80783, 1)] : List FactorBlock).map factorBlockValue).prod) = 947678621413 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_67
      · exact prime_oneHundredFiveCY_14591
      · exact prime_oneHundredFiveCY_80783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 947678621413) ^ 473839310706 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 947678621413) ^ 315892873804 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 947678621413) ^ 14144457036 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 947678621413) ^ 64949532 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 947678621413) ^ 11731164 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1644913125451 : Nat.Prime 1644913125451 := by
  apply lucas_primality 1644913125451 (2 : ZMod 1644913125451)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 2), (7, 1), (337, 1), (172171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 2), (7, 1), (337, 1), (172171, 1)] : List FactorBlock).map factorBlockValue).prod) = 1644913125451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_337
      · exact prime_oneHundredFiveCY_172171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1644913125451) ^ 822456562725 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644913125451) ^ 548304375150 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644913125451) ^ 328982625090 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644913125451) ^ 234987589350 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644913125451) ^ 4881047850 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1644913125451) ^ 9553950 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2147275852489 : Nat.Prime 2147275852489 := by
  apply lucas_primality 2147275852489 (7 : ZMod 2147275852489)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (17, 1), (19, 1), (41, 1), (211, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (17, 1), (19, 1), (41, 1), (211, 1), (821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2147275852489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_41
      · exact prime_oneHundredFiveCY_211
      · exact prime_oneHundredFiveCY_821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2147275852489) ^ 1073637926244 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 715758617496 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 165175065576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 126310344264 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 113014518552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 52372581768 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 10176662808 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2147275852489) ^ 2615439528 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2206738207199 : Nat.Prime 2206738207199 := by
  apply lucas_primality 2206738207199 (7 : ZMod 2206738207199)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (31, 1), (57383, 1), (88609, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (31, 1), (57383, 1), (88609, 1)] : List FactorBlock).map factorBlockValue).prod) = 2206738207199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_57383
      · exact prime_oneHundredFiveCY_88609
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2206738207199) ^ 1103369103599 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2206738207199) ^ 315248315314 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2206738207199) ^ 71185103458 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2206738207199) ^ 38456306 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2206738207199) ^ 24904222 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2317682119507 : Nat.Prime 2317682119507 := by
  apply lucas_primality 2317682119507 (2 : ZMod 2317682119507)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (97, 1), (307, 1), (997813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (97, 1), (307, 1), (997813, 1)] : List FactorBlock).map factorBlockValue).prod) = 2317682119507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_97
      · exact prime_oneHundredFiveCY_307
      · exact prime_oneHundredFiveCY_997813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2317682119507) ^ 1158841059753 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 772560706502 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 178283239962 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 23893630098 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 7549453158 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2317682119507) ^ 2322762 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2598617512397 : Nat.Prime 2598617512397 := by
  apply lucas_primality 2598617512397 (2 : ZMod 2598617512397)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (649654378099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (649654378099, 1)] : List FactorBlock).map factorBlockValue).prod) = 2598617512397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_649654378099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 2598617512397) ^ 1299308756198 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2598617512397) ^ 4 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2669460224903 : Nat.Prime 2669460224903 := by
  apply lucas_primality 2669460224903 (5 : ZMod 2669460224903)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (25243, 1), (1429061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (25243, 1), (1429061, 1)] : List FactorBlock).map factorBlockValue).prod) = 2669460224903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_25243
      · exact prime_oneHundredFiveCY_1429061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 2669460224903) ^ 1334730112451 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669460224903) ^ 72147573646 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669460224903) ^ 105750514 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2669460224903) ^ 1867982 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3623493255761 : Nat.Prime 3623493255761 := by
  apply lucas_primality 3623493255761 (3 : ZMod 3623493255761)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (7, 1), (1129, 1), (1279, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (7, 1), (1129, 1), (1279, 1), (4481, 1)] : List FactorBlock).map factorBlockValue).prod) = 3623493255761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_1129
      · exact prime_oneHundredFiveCY_1279
      · exact prime_oneHundredFiveCY_4481
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3623493255761) ^ 1811746627880 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623493255761) ^ 724698651152 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623493255761) ^ 517641893680 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623493255761) ^ 3209471440 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623493255761) ^ 2833067440 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3623493255761) ^ 808634960 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4133159544589 : Nat.Prime 4133159544589 := by
  apply lucas_primality 4133159544589 (6 : ZMod 4133159544589)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (96973, 1), (3551813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (96973, 1), (3551813, 1)] : List FactorBlock).map factorBlockValue).prod) = 4133159544589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_96973
      · exact prime_oneHundredFiveCY_3551813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4133159544589) ^ 2066579772294 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4133159544589) ^ 1377719848196 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4133159544589) ^ 42621756 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 4133159544589) ^ 1163676 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4232894525309 : Nat.Prime 4232894525309 := by
  apply lucas_primality 4232894525309 (2 : ZMod 4232894525309)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4232894525309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3793
      · exact prime_oneHundredFiveCY_278993839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4232894525309) ^ 2116447262654 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 1115975356 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 15172 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4375221181031 : Nat.Prime 4375221181031 := by
  apply lucas_primality 4375221181031 (14 : ZMod 4375221181031)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) = 4375221181031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_2016230959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4375221181031) ^ 2187610590515 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 875044236206 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 625031597290 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 141136167130 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 2170 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4737842238551 : Nat.Prime 4737842238551 := by
  apply lucas_primality 4737842238551 (13 : ZMod 4737842238551)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4421, 1), (21433351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4421, 1), (21433351, 1)] : List FactorBlock).map factorBlockValue).prod) = 4737842238551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_4421
      · exact prime_oneHundredFiveCY_21433351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 4737842238551) ^ 2368921119275 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4737842238551) ^ 947568447710 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4737842238551) ^ 1071667550 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 4737842238551) ^ 221050 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_5686071728479 : Nat.Prime 5686071728479 := by
  apply lucas_primality 5686071728479 (6 : ZMod 5686071728479)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (947678621413, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (947678621413, 1)] : List FactorBlock).map factorBlockValue).prod) = 5686071728479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_947678621413
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 5686071728479) ^ 2843035864239 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5686071728479) ^ 1895357242826 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 5686071728479) ^ 6 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_8097073720069 : Nat.Prime 8097073720069 := by
  apply lucas_primality 8097073720069 (2 : ZMod 8097073720069)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8097073720069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_674756143339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8097073720069) ^ 4048536860034 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 2699024573356 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_9244326521767 : Nat.Prime 9244326521767 := by
  apply lucas_primality 9244326521767 (5 : ZMod 9244326521767)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 2), (46591, 1), (674879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 2), (46591, 1), (674879, 1)] : List FactorBlock).map factorBlockValue).prod) = 9244326521767 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_46591
      · exact prime_oneHundredFiveCY_674879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 9244326521767) ^ 4622163260883 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9244326521767) ^ 3081442173922 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9244326521767) ^ 1320618074538 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9244326521767) ^ 198414426 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 9244326521767) ^ 13697754 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_9623812659437 : Nat.Prime 9623812659437 := by
  apply lucas_primality 9623812659437 (2 : ZMod 9623812659437)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (59, 1), (263, 1), (155052727, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (59, 1), (263, 1), (155052727, 1)] : List FactorBlock).map factorBlockValue).prod) = 9623812659437 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_59
      · exact prime_oneHundredFiveCY_263
      · exact prime_oneHundredFiveCY_155052727
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9623812659437) ^ 4811906329718 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9623812659437) ^ 163115468804 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9623812659437) ^ 36592443572 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 9623812659437) ^ 62068 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_10663432953857 : Nat.Prime 10663432953857 := by
  apply lucas_primality 10663432953857 (3 : ZMod 10663432953857)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 13), (2593, 1), (502001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 13), (2593, 1), (502001, 1)] : List FactorBlock).map factorBlockValue).prod) = 10663432953857 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_2593
      · exact prime_oneHundredFiveCY_502001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10663432953857) ^ 5331716476928 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10663432953857) ^ 4112392192 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 10663432953857) ^ 21241856 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_15117809801753 : Nat.Prime 15117809801753 := by
  apply lucas_primality 15117809801753 (3 : ZMod 15117809801753)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (307, 1), (6883, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (307, 1), (6883, 1), (18251, 1)] : List FactorBlock).map factorBlockValue).prod) = 15117809801753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_307
      · exact prime_oneHundredFiveCY_6883
      · exact prime_oneHundredFiveCY_18251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15117809801753) ^ 7558904900876 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15117809801753) ^ 2159687114536 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15117809801753) ^ 49243680136 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15117809801753) ^ 2196398344 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 15117809801753) ^ 828327752 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_16832038635521 : Nat.Prime 16832038635521 := by
  apply lucas_primality 16832038635521 (3 : ZMod 16832038635521)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 11), (5, 1), (1643753773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 11), (5, 1), (1643753773, 1)] : List FactorBlock).map factorBlockValue).prod) = 16832038635521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_1643753773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 16832038635521) ^ 8416019317760 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 16832038635521) ^ 3366407727104 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 16832038635521) ^ 10240 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_19210026562297 : Nat.Prime 19210026562297 := by
  apply lucas_primality 19210026562297 (5 : ZMod 19210026562297)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (5333, 1), (8828689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (5333, 1), (8828689, 1)] : List FactorBlock).map factorBlockValue).prod) = 19210026562297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_5333
      · exact prime_oneHundredFiveCY_8828689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 19210026562297) ^ 9605013281148 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19210026562297) ^ 6403342187432 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19210026562297) ^ 1130001562488 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19210026562297) ^ 3602105112 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 19210026562297) ^ 2175864 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_21232835263921 : Nat.Prime 21232835263921 := by
  apply lucas_primality 21232835263921 (11 : ZMod 21232835263921)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (73, 1), (173131403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (73, 1), (173131403, 1)] : List FactorBlock).map factorBlockValue).prod) = 21232835263921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_73
      · exact prime_oneHundredFiveCY_173131403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 21232835263921) ^ 10616417631960 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 7077611754640 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 4246567052784 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 3033262180560 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 290860757040 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 21232835263921) ^ 122640 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_47
      · exact prime_oneHundredFiveCY_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_47061672383657 : Nat.Prime 47061672383657 := by
  apply lucas_primality 47061672383657 (3 : ZMod 47061672383657)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 2), (120055286693, 1)] : List FactorBlock).map factorBlockValue).prod) = 47061672383657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_120055286693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 47061672383657) ^ 23530836191828 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 6723096054808 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 47061672383657) ^ 392 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_47111478990451 : Nat.Prime 47111478990451 := by
  apply lucas_primality 47111478990451 (2 : ZMod 47111478990451)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (7, 1), (44868075229, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (7, 1), (44868075229, 1)] : List FactorBlock).map factorBlockValue).prod) = 47111478990451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_44868075229
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47111478990451) ^ 23555739495225 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 15703826330150 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 9422295798090 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 6730211284350 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 47111478990451) ^ 1050 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_49362739139099 : Nat.Prime 49362739139099 := by
  apply lucas_primality 49362739139099 (6 : ZMod 49362739139099)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (17, 1), (23, 1), (819788407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (17, 1), (23, 1), (819788407, 1)] : List FactorBlock).map factorBlockValue).prod) = 49362739139099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_819788407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 49362739139099) ^ 24681369569549 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 49362739139099) ^ 7051819877014 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 49362739139099) ^ 4487521739918 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 49362739139099) ^ 2903690537594 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 49362739139099) ^ 2146206049526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 49362739139099) ^ 60214 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_50948517533153 : Nat.Prime 50948517533153 := by
  apply lucas_primality 50948517533153 (3 : ZMod 50948517533153)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (23, 1), (1033, 1), (67012129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (23, 1), (1033, 1), (67012129, 1)] : List FactorBlock).map factorBlockValue).prod) = 50948517533153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_1033
      · exact prime_oneHundredFiveCY_67012129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 50948517533153) ^ 25474258766576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 50948517533153) ^ 2215152936224 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 50948517533153) ^ 49320926944 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 50948517533153) ^ 760288 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_62346193038617 : Nat.Prime 62346193038617 := by
  apply lucas_primality 62346193038617 (3 : ZMod 62346193038617)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (163, 1), (15259, 1), (3133331, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (163, 1), (15259, 1), (3133331, 1)] : List FactorBlock).map factorBlockValue).prod) = 62346193038617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_163
      · exact prime_oneHundredFiveCY_15259
      · exact prime_oneHundredFiveCY_3133331
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 62346193038617) ^ 31173096519308 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 62346193038617) ^ 382491981832 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 62346193038617) ^ 4085863624 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 62346193038617) ^ 19897736 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_68449169782753 : Nat.Prime 68449169782753 := by
  apply lucas_primality 68449169782753 (5 : ZMod 68449169782753)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (37, 1), (1751872691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (37, 1), (1751872691, 1)] : List FactorBlock).map factorBlockValue).prod) = 68449169782753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_1751872691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68449169782753) ^ 34224584891376 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68449169782753) ^ 22816389927584 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68449169782753) ^ 6222651798432 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68449169782753) ^ 1849977561696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 68449169782753) ^ 39072 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_91387916234123 : Nat.Prime 91387916234123 := by
  apply lucas_primality 91387916234123 (2 : ZMod 91387916234123)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (229, 1), (4457, 1), (6679, 1), (6703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (229, 1), (4457, 1), (6679, 1), (6703, 1)] : List FactorBlock).map factorBlockValue).prod) = 91387916234123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_229
      · exact prime_oneHundredFiveCY_4457
      · exact prime_oneHundredFiveCY_6679
      · exact prime_oneHundredFiveCY_6703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 91387916234123) ^ 45693958117061 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91387916234123) ^ 399073870018 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91387916234123) ^ 20504356346 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91387916234123) ^ 13682874118 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 91387916234123) ^ 13633882774 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_100257985466497 : Nat.Prime 100257985466497 := by
  apply lucas_primality 100257985466497 (5 : ZMod 100257985466497)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (11, 1), (13, 1), (19, 1), (173, 1), (185153, 1)] : List FactorBlock).map factorBlockValue).prod) = 100257985466497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_173
      · exact prime_oneHundredFiveCY_185153
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 100257985466497) ^ 50128992733248 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 33419328488832 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 9114362315136 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 7712152728192 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 5276736077184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 579525927552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 100257985466497) ^ 541487232 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_124412422266809 : Nat.Prime 124412422266809 := by
  apply lucas_primality 124412422266809 (3 : ZMod 124412422266809)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (199, 1), (6011423573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (199, 1), (6011423573, 1)] : List FactorBlock).map factorBlockValue).prod) = 124412422266809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_199
      · exact prime_oneHundredFiveCY_6011423573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 124412422266809) ^ 62206211133404 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124412422266809) ^ 9570186328216 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124412422266809) ^ 625188051592 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124412422266809) ^ 20696 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_148781335582813 : Nat.Prime 148781335582813 := by
  apply lucas_primality 148781335582813 (2 : ZMod 148781335582813)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (277, 1), (630418703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (277, 1), (630418703, 1)] : List FactorBlock).map factorBlockValue).prod) = 148781335582813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_71
      · exact prime_oneHundredFiveCY_277
      · exact prime_oneHundredFiveCY_630418703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 148781335582813) ^ 74390667791406 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 49593778527604 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 2095511768772 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 537116734956 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 148781335582813) ^ 236004 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_204285462728549 : Nat.Prime 204285462728549 := by
  apply lucas_primality 204285462728549 (2 : ZMod 204285462728549)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) = 204285462728549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_46381
      · exact prime_oneHundredFiveCY_1101126877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204285462728549) ^ 102142731364274 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 4404507508 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 185524 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_209520105344321 : Nat.Prime 209520105344321 := by
  apply lucas_primality 209520105344321 (3 : ZMod 209520105344321)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (5, 1), (58963, 1), (11104427, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (5, 1), (58963, 1), (11104427, 1)] : List FactorBlock).map factorBlockValue).prod) = 209520105344321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_58963
      · exact prime_oneHundredFiveCY_11104427
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 209520105344321) ^ 104760052672160 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 41904021068864 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 3553416640 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 209520105344321) ^ 18868160 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_254753821265093 : Nat.Prime 254753821265093 := by
  apply lucas_primality 254753821265093 (2 : ZMod 254753821265093)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (79, 1), (806182978687, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (79, 1), (806182978687, 1)] : List FactorBlock).map factorBlockValue).prod) = 254753821265093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_79
      · exact prime_oneHundredFiveCY_806182978687
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 254753821265093) ^ 127376910632546 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254753821265093) ^ 3224731914748 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 254753821265093) ^ 316 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_273308408322643 : Nat.Prime 273308408322643 := by
  apply lucas_primality 273308408322643 (3 : ZMod 273308408322643)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (1109, 1), (5273, 1), (33721, 1)] : List FactorBlock).map factorBlockValue).prod) = 273308408322643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_1109
      · exact prime_oneHundredFiveCY_5273
      · exact prime_oneHundredFiveCY_33721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 273308408322643) ^ 136654204161321 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 91102802774214 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 39044058331806 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 24846218938422 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 246445814538 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 51831672354 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 273308408322643) ^ 8104991202 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_289213356673357 : Nat.Prime 289213356673357 := by
  apply lucas_primality 289213356673357 (2 : ZMod 289213356673357)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (37, 1), (8933, 1), (72918553, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (37, 1), (8933, 1), (72918553, 1)] : List FactorBlock).map factorBlockValue).prod) = 289213356673357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_8933
      · exact prime_oneHundredFiveCY_72918553
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 289213356673357) ^ 144606678336678 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289213356673357) ^ 96404452224452 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289213356673357) ^ 7816577207388 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289213356673357) ^ 32375837532 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 289213356673357) ^ 3966252 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_352856105336047 : Nat.Prime 352856105336047 := by
  apply lucas_primality 352856105336047 (3 : ZMod 352856105336047)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (139, 1), (2503484351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (139, 1), (2503484351, 1)] : List FactorBlock).map factorBlockValue).prod) = 352856105336047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_139
      · exact prime_oneHundredFiveCY_2503484351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 352856105336047) ^ 176428052668023 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 117618701778682 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 27142777333542 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 2538533131914 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 352856105336047) ^ 140946 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_370372159271287 : Nat.Prime 370372159271287 := by
  apply lucas_primality 370372159271287 (5 : ZMod 370372159271287)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (19, 1), (14621, 1), (24689591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (19, 1), (14621, 1), (24689591, 1)] : List FactorBlock).map factorBlockValue).prod) = 370372159271287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_14621
      · exact prime_oneHundredFiveCY_24689591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 370372159271287) ^ 185186079635643 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 370372159271287) ^ 123457386423762 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 370372159271287) ^ 19493271540594 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 370372159271287) ^ 25331520366 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 370372159271287) ^ 15001146 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_382191034750579 : Nat.Prime 382191034750579 := by
  apply lucas_primality 382191034750579 (3 : ZMod 382191034750579)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (21232835263921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (21232835263921, 1)] : List FactorBlock).map factorBlockValue).prod) = 382191034750579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_21232835263921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 382191034750579) ^ 191095517375289 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 382191034750579) ^ 127397011583526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 382191034750579) ^ 18 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_406089744580621 : Nat.Prime 406089744580621 := by
  apply lucas_primality 406089744580621 (2 : ZMod 406089744580621)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (31, 1), (33757, 1), (2155877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (31, 1), (33757, 1), (2155877, 1)] : List FactorBlock).map factorBlockValue).prod) = 406089744580621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_33757
      · exact prime_oneHundredFiveCY_2155877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 406089744580621) ^ 203044872290310 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 406089744580621) ^ 135363248193540 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 406089744580621) ^ 81217948916124 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 406089744580621) ^ 13099669180020 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 406089744580621) ^ 12029793660 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 406089744580621) ^ 188364060 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_592870936031993 : Nat.Prime 592870936031993 := by
  apply lucas_primality 592870936031993 (3 : ZMod 592870936031993)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (19, 1), (67, 1), (1439, 1), (40455817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (19, 1), (67, 1), (1439, 1), (40455817, 1)] : List FactorBlock).map factorBlockValue).prod) = 592870936031993 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_67
      · exact prime_oneHundredFiveCY_1439
      · exact prime_oneHundredFiveCY_40455817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 592870936031993) ^ 296435468015996 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 592870936031993) ^ 31203733475368 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 592870936031993) ^ 8848819940776 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 592870936031993) ^ 412002040328 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 592870936031993) ^ 14654776 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_701
      · exact prime_oneHundredFiveCY_9769
      · exact prime_oneHundredFiveCY_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_621760403722501 : Nat.Prime 621760403722501 := by
  apply lucas_primality 621760403722501 (26 : ZMod 621760403722501)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) = 621760403722501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_59
      · exact prime_oneHundredFiveCY_66909917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 621760403722501) ^ 310880201861250 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 207253467907500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 124352080744500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 88822914817500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 10538311927500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 9292500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1049880536621731 : Nat.Prime 1049880536621731 := by
  apply lucas_primality 1049880536621731 (10 : ZMod 1049880536621731)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (11, 1), (59, 1), (17974328653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (11, 1), (59, 1), (17974328653, 1)] : List FactorBlock).map factorBlockValue).prod) = 1049880536621731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_59
      · exact prime_oneHundredFiveCY_17974328653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 1049880536621731) ^ 524940268310865 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1049880536621731) ^ 349960178873910 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1049880536621731) ^ 209976107324346 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1049880536621731) ^ 95443685147430 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1049880536621731) ^ 17794585366470 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 1049880536621731) ^ 58410 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1342986505854263 : Nat.Prime 1342986505854263 := by
  apply lucas_primality 1342986505854263 (5 : ZMod 1342986505854263)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19489, 1), (34454987579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19489, 1), (34454987579, 1)] : List FactorBlock).map factorBlockValue).prod) = 1342986505854263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_19489
      · exact prime_oneHundredFiveCY_34454987579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1342986505854263) ^ 671493252927131 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1342986505854263) ^ 68909975158 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 1342986505854263) ^ 38978 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1487813355828131 : Nat.Prime 1487813355828131 := by
  apply lucas_primality 1487813355828131 (2 : ZMod 1487813355828131)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (148781335582813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (148781335582813, 1)] : List FactorBlock).map factorBlockValue).prod) = 1487813355828131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_148781335582813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1487813355828131) ^ 743906677914065 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1487813355828131) ^ 297562671165626 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1487813355828131) ^ 10 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2242606239584497 : Nat.Prime 2242606239584497 := by
  apply lucas_primality 2242606239584497 (5 : ZMod 2242606239584497)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (223, 1), (479, 1), (3881, 1), (37567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (223, 1), (479, 1), (3881, 1), (37567, 1)] : List FactorBlock).map factorBlockValue).prod) = 2242606239584497 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_223
      · exact prime_oneHundredFiveCY_479
      · exact prime_oneHundredFiveCY_3881
      · exact prime_oneHundredFiveCY_37567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2242606239584497) ^ 1121303119792248 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2242606239584497) ^ 747535413194832 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2242606239584497) ^ 10056530222352 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2242606239584497) ^ 4681850187024 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2242606239584497) ^ 577842370416 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2242606239584497) ^ 59696175888 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2765409987722617 : Nat.Prime 2765409987722617 := by
  apply lucas_primality 2765409987722617 (10 : ZMod 2765409987722617)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (13, 1), (19, 3), (97, 1), (167, 1), (26591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (13, 1), (19, 3), (97, 1), (167, 1), (26591, 1)] : List FactorBlock).map factorBlockValue).prod) = 2765409987722617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_97
      · exact prime_oneHundredFiveCY_167
      · exact prime_oneHundredFiveCY_26591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2765409987722617) ^ 1382704993861308 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 921803329240872 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 212723845209432 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 145547894090664 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 28509381316728 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 16559341243848 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 2765409987722617) ^ 103997968776 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3687551624579369 : Nat.Prime 3687551624579369 := by
  apply lucas_primality 3687551624579369 (6 : ZMod 3687551624579369)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (13, 1), (37, 1), (109, 1), (1255967807, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (13, 1), (37, 1), (109, 1), (1255967807, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687551624579369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_109
      · exact prime_oneHundredFiveCY_1255967807
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 3687551624579369) ^ 1843775812289684 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3687551624579369) ^ 526793089225624 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3687551624579369) ^ 283657817275336 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3687551624579369) ^ 99663557421064 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3687551624579369) ^ 33830748849352 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 3687551624579369) ^ 2936024 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4051062291545369 : Nat.Prime 4051062291545369 := by
  apply lucas_primality 4051062291545369 (3 : ZMod 4051062291545369)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (31, 1), (241, 1), (503, 1), (12250097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (31, 1), (241, 1), (503, 1), (12250097, 1)] : List FactorBlock).map factorBlockValue).prod) = 4051062291545369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_241
      · exact prime_oneHundredFiveCY_503
      · exact prime_oneHundredFiveCY_12250097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4051062291545369) ^ 2025531145772684 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4051062291545369) ^ 368278390140488 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4051062291545369) ^ 130679428759528 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4051062291545369) ^ 16809387101848 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4051062291545369) ^ 8053801772456 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4051062291545369) ^ 330696344 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4250290743667637 : Nat.Prime 4250290743667637 := by
  apply lucas_primality 4250290743667637 (2 : ZMod 4250290743667637)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (902389, 1), (31824613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (902389, 1), (31824613, 1)] : List FactorBlock).map factorBlockValue).prod) = 4250290743667637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_37
      · exact prime_oneHundredFiveCY_902389
      · exact prime_oneHundredFiveCY_31824613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4250290743667637) ^ 2125145371833818 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 114872722801828 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 4710042724 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4250290743667637) ^ 133553572 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_6217604037225011 : Nat.Prime 6217604037225011 := by
  apply lucas_primality 6217604037225011 (2 : ZMod 6217604037225011)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) = 6217604037225011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_621760403722501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6217604037225011) ^ 3108802018612505 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 1243520807445002 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 10 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_7109287631275139 : Nat.Prime 7109287631275139 := by
  apply lucas_primality 7109287631275139 (2 : ZMod 7109287631275139)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (167, 1), (283, 1), (887, 1), (84794867, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (167, 1), (283, 1), (887, 1), (84794867, 1)] : List FactorBlock).map factorBlockValue).prod) = 7109287631275139 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_167
      · exact prime_oneHundredFiveCY_283
      · exact prime_oneHundredFiveCY_887
      · exact prime_oneHundredFiveCY_84794867
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7109287631275139) ^ 3554643815637569 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7109287631275139) ^ 42570584618414 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7109287631275139) ^ 25121157707686 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7109287631275139) ^ 8014980418574 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7109287631275139) ^ 83841014 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_7375103249158739 : Nat.Prime 7375103249158739 := by
  apply lucas_primality 7375103249158739 (2 : ZMod 7375103249158739)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3687551624579369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3687551624579369, 1)] : List FactorBlock).map factorBlockValue).prod) = 7375103249158739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3687551624579369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7375103249158739) ^ 3687551624579369 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 7375103249158739) ^ 2 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_8926880134968787 : Nat.Prime 8926880134968787 := by
  apply lucas_primality 8926880134968787 (2 : ZMod 8926880134968787)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1487813355828131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1487813355828131, 1)] : List FactorBlock).map factorBlockValue).prod) = 8926880134968787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1487813355828131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8926880134968787) ^ 4463440067484393 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926880134968787) ^ 2975626711656262 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 8926880134968787) ^ 6 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_12452009194005137 : Nat.Prime 12452009194005137 := by
  apply lucas_primality 12452009194005137 (3 : ZMod 12452009194005137)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (197, 1), (743, 1), (759567493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (197, 1), (743, 1), (759567493, 1)] : List FactorBlock).map factorBlockValue).prod) = 12452009194005137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_197
      · exact prime_oneHundredFiveCY_743
      · exact prime_oneHundredFiveCY_759567493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12452009194005137) ^ 6226004597002568 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 1778858456286448 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 63208168497488 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 16759097165552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 16393552 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_12541816931536903 : Nat.Prime 12541816931536903 := by
  apply lucas_primality 12541816931536903 (6 : ZMod 12541816931536903)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (26449, 1), (79031450033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (26449, 1), (79031450033, 1)] : List FactorBlock).map factorBlockValue).prod) = 12541816931536903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_26449
      · exact prime_oneHundredFiveCY_79031450033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 12541816931536903) ^ 6270908465768451 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 12541816931536903) ^ 4180605643845634 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 12541816931536903) ^ 474188700198 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 12541816931536903) ^ 158694 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_145829
      · exact prime_oneHundredFiveCY_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_73154504292883693 : Nat.Prime 73154504292883693 := by
  apply lucas_primality 73154504292883693 (17 : ZMod 73154504292883693)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 2), (124412422266809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 2), (124412422266809, 1)] : List FactorBlock).map factorBlockValue).prod) = 73154504292883693 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_124412422266809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 73154504292883693) ^ 36577252146441846 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 73154504292883693) ^ 24384834764294564 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 73154504292883693) ^ 10450643470411956 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 73154504292883693) ^ 588 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_104620885602558571 : Nat.Prime 104620885602558571 := by
  apply lucas_primality 104620885602558571 (2 : ZMod 104620885602558571)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 2), (368077, 1), (64452701, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 2), (368077, 1), (64452701, 1)] : List FactorBlock).map factorBlockValue).prod) = 104620885602558571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_368077
      · exact prime_oneHundredFiveCY_64452701
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 104620885602558571) ^ 52310442801279285 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 104620885602558571) ^ 34873628534186190 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 104620885602558571) ^ 20924177120511714 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 104620885602558571) ^ 14945840800365510 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 104620885602558571) ^ 284236411410 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 104620885602558571) ^ 1623219570 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_160584254210685187 : Nat.Prime 160584254210685187 := by
  apply lucas_primality 160584254210685187 (3 : ZMod 160584254210685187)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (2309, 1), (183987037393, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (2309, 1), (183987037393, 1)] : List FactorBlock).map factorBlockValue).prod) = 160584254210685187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_2309
      · exact prime_oneHundredFiveCY_183987037393
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 160584254210685187) ^ 80292127105342593 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 160584254210685187) ^ 53528084736895062 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 160584254210685187) ^ 22940607744383598 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 160584254210685187) ^ 69547100134554 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 160584254210685187) ^ 872802 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_167118506749901009 : Nat.Prime 167118506749901009 := by
  apply lucas_primality 167118506749901009 (3 : ZMod 167118506749901009)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (41, 1), (254753821265093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (41, 1), (254753821265093, 1)] : List FactorBlock).map factorBlockValue).prod) = 167118506749901009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_41
      · exact prime_oneHundredFiveCY_254753821265093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 167118506749901009) ^ 83559253374950504 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 167118506749901009) ^ 4076061140241488 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 167118506749901009) ^ 656 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_335902595973800657 : Nat.Prime 335902595973800657 := by
  apply lucas_primality 335902595973800657 (3 : ZMod 335902595973800657)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) = 335902595973800657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_53
      · exact prime_oneHundredFiveCY_1559
      · exact prime_oneHundredFiveCY_97453
      · exact prime_oneHundredFiveCY_113357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335902595973800657) ^ 167951297986900328 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 14604460694513072 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 6337784829694352 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 215460292478384 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 3446816372752 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 2963227643408 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_443638688399388539 : Nat.Prime 443638688399388539 := by
  apply lucas_primality 443638688399388539 (2 : ZMod 443638688399388539)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (5573, 1), (5686071728479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (5573, 1), (5686071728479, 1)] : List FactorBlock).map factorBlockValue).prod) = 443638688399388539 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_5573
      · exact prime_oneHundredFiveCY_5686071728479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 443638688399388539) ^ 221819344199694269 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 443638688399388539) ^ 63376955485626934 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 443638688399388539) ^ 79605004198706 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 443638688399388539) ^ 78022 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_887277376798777079 : Nat.Prime 887277376798777079 := by
  apply lucas_primality 887277376798777079 (11 : ZMod 887277376798777079)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (443638688399388539, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (443638688399388539, 1)] : List FactorBlock).map factorBlockValue).prod) = 887277376798777079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_443638688399388539
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (11 : ZMod 887277376798777079) ^ 443638688399388539 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (11 : ZMod 887277376798777079) ^ 2 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1033556399581327493 : Nat.Prime 1033556399581327493 := by
  apply lucas_primality 1033556399581327493 (2 : ZMod 1033556399581327493)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (6211, 1), (20899, 1), (153124189, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (6211, 1), (20899, 1), (153124189, 1)] : List FactorBlock).map factorBlockValue).prod) = 1033556399581327493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_6211
      · exact prime_oneHundredFiveCY_20899
      · exact prime_oneHundredFiveCY_153124189
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1033556399581327493) ^ 516778199790663746 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033556399581327493) ^ 79504338429332884 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033556399581327493) ^ 166407406147372 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033556399581327493) ^ 49454825569708 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1033556399581327493) ^ 6749791828 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2775812652630538943 : Nat.Prime 2775812652630538943 := by
  apply lucas_primality 2775812652630538943 (5 : ZMod 2775812652630538943)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (777122653, 1), (1785955307, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (777122653, 1), (1785955307, 1)] : List FactorBlock).map factorBlockValue).prod) = 2775812652630538943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_777122653
      · exact prime_oneHundredFiveCY_1785955307
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2775812652630538943) ^ 1387906326315269471 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2775812652630538943) ^ 3571910614 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 2775812652630538943) ^ 1554245306 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3365623024283972887 : Nat.Prime 3365623024283972887 := by
  apply lucas_primality 3365623024283972887 (3 : ZMod 3365623024283972887)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (31, 1), (1499, 1), (101438759971, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (31, 1), (1499, 1), (101438759971, 1)] : List FactorBlock).map factorBlockValue).prod) = 3365623024283972887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_1499
      · exact prime_oneHundredFiveCY_101438759971
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3365623024283972887) ^ 1682811512141986443 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 1121874341427990962 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 480803289183424698 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 197977824957880758 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 108568484654321706 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 2245245513198114 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 3365623024283972887) ^ 33178866 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4251781223518704301 : Nat.Prime 4251781223518704301 := by
  apply lucas_primality 4251781223518704301 (2 : ZMod 4251781223518704301)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 2), (127, 1), (4133159544589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 2), (127, 1), (4133159544589, 1)] : List FactorBlock).map factorBlockValue).prod) = 4251781223518704301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_127
      · exact prime_oneHundredFiveCY_4133159544589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4251781223518704301) ^ 2125890611759352150 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4251781223518704301) ^ 1417260407839568100 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4251781223518704301) ^ 850356244703740860 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4251781223518704301) ^ 33478592311170900 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4251781223518704301) ^ 1028700 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4527184655447032079 : Nat.Prime 4527184655447032079 := by
  apply lucas_primality 4527184655447032079 (7 : ZMod 4527184655447032079)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (5821, 1), (152597, 1), (110796689, 1)] : List FactorBlock).map factorBlockValue).prod) = 4527184655447032079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_5821
      · exact prime_oneHundredFiveCY_152597
      · exact prime_oneHundredFiveCY_110796689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 4527184655447032079) ^ 2263592327723516039 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 196834115454218786 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 777733148161318 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 29667586226774 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 4527184655447032079) ^ 40860288302 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_6815633209915294781 : Nat.Prime 6815633209915294781 := by
  apply lucas_primality 6815633209915294781 (2 : ZMod 6815633209915294781)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1376699, 1), (247535343961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1376699, 1), (247535343961, 1)] : List FactorBlock).map factorBlockValue).prod) = 6815633209915294781 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_1376699
      · exact prime_oneHundredFiveCY_247535343961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6815633209915294781) ^ 3407816604957647390 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6815633209915294781) ^ 1363126641983058956 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6815633209915294781) ^ 4950706879220 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 6815633209915294781) ^ 27533980 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_36265159998777480317 : Nat.Prime 36265159998777480317 := by
  apply lucas_primality 36265159998777480317 (5 : ZMod 36265159998777480317)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (13, 1), (29, 1), (73, 1), (47061672383657, 1)] : List FactorBlock).map factorBlockValue).prod) = 36265159998777480317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_73
      · exact prime_oneHundredFiveCY_47061672383657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 36265159998777480317) ^ 18132579999388740158 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 5180737142682497188 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 2789627692213652332 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 1250522758578533804 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 496783013681883292 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 36265159998777480317) ^ 770588 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_52983531609217552957 : Nat.Prime 52983531609217552957 := by
  apply lucas_primality 52983531609217552957 (5 : ZMod 52983531609217552957)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2063, 1), (15269, 1), (140168308879, 1)] : List FactorBlock).map factorBlockValue).prod) = 52983531609217552957 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_2063
      · exact prime_oneHundredFiveCY_15269
      · exact prime_oneHundredFiveCY_140168308879
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 52983531609217552957) ^ 26491765804608776478 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 17661177203072517652 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 25682758899281412 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 3470006654608524 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 52983531609217552957) ^ 377999364 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_76364612785197585103 : Nat.Prime 76364612785197585103 := by
  apply lucas_primality 76364612785197585103 (5 : ZMod 76364612785197585103)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) = 76364612785197585103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_89
      · exact prime_oneHundredFiveCY_6217604037225011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76364612785197585103) ^ 38182306392598792551 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 25454870928399195034 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 3320200555878155874 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 858029357137051518 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 12282 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_85908525773731090511 : Nat.Prime 85908525773731090511 := by
  apply lucas_primality 85908525773731090511 (7 : ZMod 85908525773731090511)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (29, 1), (53, 1), (3739, 1), (68113, 1), (21947089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (29, 1), (53, 1), (3739, 1), (68113, 1), (21947089, 1)] : List FactorBlock).map factorBlockValue).prod) = 85908525773731090511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_53
      · exact prime_oneHundredFiveCY_3739
      · exact prime_oneHundredFiveCY_68113
      · exact prime_oneHundredFiveCY_21947089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 85908525773731090511) ^ 42954262886865545255 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 17181705154746218102 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 2962362957714865190 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 1620915580636435670 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 22976337462886090 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 1261264747900270 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 85908525773731090511) ^ 3914347172590 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_87757496123468850851 : Nat.Prime 87757496123468850851 := by
  apply lucas_primality 87757496123468850851 (2 : ZMod 87757496123468850851)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (8377, 1), (209520105344321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (8377, 1), (209520105344321, 1)] : List FactorBlock).map factorBlockValue).prod) = 87757496123468850851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_8377
      · exact prime_oneHundredFiveCY_209520105344321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 87757496123468850851) ^ 43878748061734425425 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 17551499224693770170 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 10476005267216050 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 87757496123468850851) ^ 418850 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_100264199591013889591 : Nat.Prime 100264199591013889591 := by
  apply lucas_primality 100264199591013889591 (3 : ZMod 100264199591013889591)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (5, 1), (181, 1), (1697, 1), (402995739827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (5, 1), (181, 1), (1697, 1), (402995739827, 1)] : List FactorBlock).map factorBlockValue).prod) = 100264199591013889591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_181
      · exact prime_oneHundredFiveCY_1697
      · exact prime_oneHundredFiveCY_402995739827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 100264199591013889591) ^ 50132099795506944795 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 100264199591013889591) ^ 33421399863671296530 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 100264199591013889591) ^ 20052839918202777918 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 100264199591013889591) ^ 553945854093999390 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 100264199591013889591) ^ 59083205416036470 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 100264199591013889591) ^ 248797170 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_73
      · exact prime_oneHundredFiveCY_79
      · exact prime_oneHundredFiveCY_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_6863
      · exact prime_oneHundredFiveCY_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_297534392471966499847 : Nat.Prime 297534392471966499847 := by
  apply lucas_primality 297534392471966499847 (33 : ZMod 297534392471966499847)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (48131, 1), (1868173, 1), (183832669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (48131, 1), (1868173, 1), (183832669, 1)] : List FactorBlock).map factorBlockValue).prod) = 297534392471966499847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_48131
      · exact prime_oneHundredFiveCY_1868173
      · exact prime_oneHundredFiveCY_183832669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (33 : ZMod 297534392471966499847) ^ 148767196235983249923 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 99178130823988833282 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 6181762117387266 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 159264903449502 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (33 : ZMod 297534392471966499847) ^ 1618506623934 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_299875528248665142247 : Nat.Prime 299875528248665142247 := by
  apply lucas_primality 299875528248665142247 (3 : ZMod 299875528248665142247)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (31, 1), (53, 1), (2765409987722617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (31, 1), (53, 1), (2765409987722617, 1)] : List FactorBlock).map factorBlockValue).prod) = 299875528248665142247 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_53
      · exact prime_oneHundredFiveCY_2765409987722617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 299875528248665142247) ^ 149937764124332571123 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 299875528248665142247) ^ 99958509416221714082 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 299875528248665142247) ^ 27261411658969558386 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 299875528248665142247) ^ 9673404137053714266 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 299875528248665142247) ^ 5658028834880474382 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 299875528248665142247) ^ 108438 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_385042035699220627919 : Nat.Prime 385042035699220627919 := by
  apply lucas_primality 385042035699220627919 (7 : ZMod 385042035699220627919)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (85847, 1), (2242606239584497, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (85847, 1), (2242606239584497, 1)] : List FactorBlock).map factorBlockValue).prod) = 385042035699220627919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_85847
      · exact prime_oneHundredFiveCY_2242606239584497
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 385042035699220627919) ^ 192521017849610313959 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 385042035699220627919) ^ 4485212479168994 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 385042035699220627919) ^ 171694 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_575284891189512700303 : Nat.Prime 575284891189512700303 := by
  apply lucas_primality 575284891189512700303 (5 : ZMod 575284891189512700303)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) = 575284891189512700303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1709
      · exact prime_oneHundredFiveCY_12823
      · exact prime_oneHundredFiveCY_4375221181031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 575284891189512700303) ^ 287642445594756350151 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 191761630396504233434 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 336620767226163078 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 44863517990291874 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 131487042 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_818253362794063446907 : Nat.Prime 818253362794063446907 := by
  apply lucas_primality 818253362794063446907 (2 : ZMod 818253362794063446907)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (313, 1), (13933, 1), (1079879, 1), (1524119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (313, 1), (13933, 1), (1079879, 1), (1524119, 1)] : List FactorBlock).map factorBlockValue).prod) = 818253362794063446907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_313
      · exact prime_oneHundredFiveCY_13933
      · exact prime_oneHundredFiveCY_1079879
      · exact prime_oneHundredFiveCY_1524119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 818253362794063446907) ^ 409126681397031723453 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 272751120931354482302 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 43065966462845444574 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 2614227996147167562 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 58727722873326882 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 757726896063414 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 818253362794063446907) ^ 536869734445974 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_829821849978416232493 : Nat.Prime 829821849978416232493 := by
  apply lucas_primality 829821849978416232493 (5 : ZMod 829821849978416232493)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (127, 1), (947, 1), (11437, 1), (1861975811, 1)] : List FactorBlock).map factorBlockValue).prod) = 829821849978416232493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_127
      · exact prime_oneHundredFiveCY_947
      · exact prime_oneHundredFiveCY_11437
      · exact prime_oneHundredFiveCY_1861975811
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 829821849978416232493) ^ 414910924989208116246 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 276607283326138744164 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 6534030314790678996 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 876263833134547236 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 72555901895463516 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 829821849978416232493) ^ 445667363172 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1070234160607999544869 : Nat.Prime 1070234160607999544869 := by
  apply lucas_primality 1070234160607999544869 (2 : ZMod 1070234160607999544869)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (43, 1), (4584901, 1), (16754650799, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (43, 1), (4584901, 1), (16754650799, 1)] : List FactorBlock).map factorBlockValue).prod) = 1070234160607999544869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_4584901
      · exact prime_oneHundredFiveCY_16754650799
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1070234160607999544869) ^ 535117080303999772434 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070234160607999544869) ^ 356744720202666514956 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070234160607999544869) ^ 24889166525767431276 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070234160607999544869) ^ 233425794931668 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1070234160607999544869) ^ 63876840732 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1081687868363620552253 : Nat.Prime 1081687868363620552253 := by
  apply lucas_primality 1081687868363620552253 (2 : ZMod 1081687868363620552253)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (71, 1), (199, 1), (52864081, 1), (362051087, 1)] : List FactorBlock).map factorBlockValue).prod) = 1081687868363620552253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_71
      · exact prime_oneHundredFiveCY_199
      · exact prime_oneHundredFiveCY_52864081
      · exact prime_oneHundredFiveCY_362051087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1081687868363620552253) ^ 540843934181810276126 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 15235040399487613412 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 5435617428962917348 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 20461679232892 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1081687868363620552253) ^ 2987666401796 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_1549
      · exact prime_oneHundredFiveCY_47713
      · exact prime_oneHundredFiveCY_341461
      · exact prime_oneHundredFiveCY_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2095345349788425739783 : Nat.Prime 2095345349788425739783 := by
  apply lucas_primality 2095345349788425739783 (7 : ZMod 2095345349788425739783)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (47, 1), (120623, 1), (3623493255761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (47, 1), (120623, 1), (3623493255761, 1)] : List FactorBlock).map factorBlockValue).prod) = 2095345349788425739783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_47
      · exact prime_oneHundredFiveCY_120623
      · exact prime_oneHundredFiveCY_3623493255761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2095345349788425739783) ^ 1047672674894212869891 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2095345349788425739783) ^ 698448449929475246594 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2095345349788425739783) ^ 123255608811083867046 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2095345349788425739783) ^ 44581815952945228506 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2095345349788425739783) ^ 17371026668118234 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 2095345349788425739783) ^ 578266662 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3019418713742564280571 : Nat.Prime 3019418713742564280571 := by
  apply lucas_primality 3019418713742564280571 (10 : ZMod 3019418713742564280571)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (97, 1), (4671071, 1), (222133410637, 1)] : List FactorBlock).map factorBlockValue).prod) = 3019418713742564280571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_97
      · exact prime_oneHundredFiveCY_4671071
      · exact prime_oneHundredFiveCY_222133410637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 3019418713742564280571) ^ 1509709356871282140285 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 1006472904580854760190 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 603883742748512856114 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 31128027976727466810 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 646408224953670 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (10 : ZMod 3019418713742564280571) ^ 13592816610 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3053393917893592837301 : Nat.Prime 3053393917893592837301 := by
  apply lucas_primality 3053393917893592837301 (2 : ZMod 3053393917893592837301)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (2775812652630538943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (2775812652630538943, 1)] : List FactorBlock).map factorBlockValue).prod) = 3053393917893592837301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_2775812652630538943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3053393917893592837301) ^ 1526696958946796418650 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 610678783578718567460 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 277581265263053894300 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3053393917893592837301) ^ 1100 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_3970959864830274425357 : Nat.Prime 3970959864830274425357 := by
  apply lucas_primality 3970959864830274425357 (2 : ZMod 3970959864830274425357)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3970959864830274425357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_76364612785197585103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3970959864830274425357) ^ 1985479932415137212678 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 305458451140790340412 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 52 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4762589087742351216833 : Nat.Prime 4762589087742351216833 := by
  apply lucas_primality 4762589087742351216833 (3 : ZMod 4762589087742351216833)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (13, 1), (197, 1), (6133, 1), (4737842238551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (13, 1), (197, 1), (6133, 1), (4737842238551, 1)] : List FactorBlock).map factorBlockValue).prod) = 4762589087742351216833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_197
      · exact prime_oneHundredFiveCY_6133
      · exact prime_oneHundredFiveCY_4737842238551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 4762589087742351216833) ^ 2381294543871175608416 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4762589087742351216833) ^ 366353006749411632064 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4762589087742351216833) ^ 24175579125595691456 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4762589087742351216833) ^ 776551294267463104 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 4762589087742351216833) ^ 1005223232 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_8993759679696815118617 : Nat.Prime 8993759679696815118617 := by
  apply lucas_primality 8993759679696815118617 (3 : ZMod 8993759679696815118617)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31, 1), (36265159998777480317, 1)] : List FactorBlock).map factorBlockValue).prod) = 8993759679696815118617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_31
      · exact prime_oneHundredFiveCY_36265159998777480317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 8993759679696815118617) ^ 4496879839848407559308 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 290121279990219842536 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 8993759679696815118617) ^ 248 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_20564180984703735386873 : Nat.Prime 20564180984703735386873 := by
  apply lucas_primality 20564180984703735386873 (3 : ZMod 20564180984703735386873)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 2), (1009, 1), (7015717, 1), (1256493827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 2), (1009, 1), (7015717, 1), (1256493827, 1)] : List FactorBlock).map factorBlockValue).prod) = 20564180984703735386873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_1009
      · exact prime_oneHundredFiveCY_7015717
      · exact prime_oneHundredFiveCY_1256493827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20564180984703735386873) ^ 10282090492351867693436 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20564180984703735386873) ^ 1209657704982572669816 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20564180984703735386873) ^ 20380754196931353208 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20564180984703735386873) ^ 2931158851576216 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 20564180984703735386873) ^ 16366320743336 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_57792644672831975422927 : Nat.Prime 57792644672831975422927 := by
  apply lucas_primality 57792644672831975422927 (5 : ZMod 57792644672831975422927)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1070234160607999544869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1070234160607999544869, 1)] : List FactorBlock).map factorBlockValue).prod) = 57792644672831975422927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_1070234160607999544869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 57792644672831975422927) ^ 28896322336415987711463 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 57792644672831975422927) ^ 19264214890943991807642 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 57792644672831975422927) ^ 54 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_102603667664945300223157 : Nat.Prime 102603667664945300223157 := by
  apply lucas_primality 102603667664945300223157 (2 : ZMod 102603667664945300223157)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2011699, 1), (4250290743667637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2011699, 1), (4250290743667637, 1)] : List FactorBlock).map factorBlockValue).prod) = 102603667664945300223157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_2011699
      · exact prime_oneHundredFiveCY_4250290743667637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 102603667664945300223157) ^ 51301833832472650111578 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 34201222554981766741052 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 51003488924011644 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 102603667664945300223157) ^ 24140388 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_103691682173163318995821 : Nat.Prime 103691682173163318995821 := by
  apply lucas_primality 103691682173163318995821 (13 : ZMod 103691682173163318995821)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (71569, 1), (1049880536621731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (71569, 1), (1049880536621731, 1)] : List FactorBlock).map factorBlockValue).prod) = 103691682173163318995821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_23
      · exact prime_oneHundredFiveCY_71569
      · exact prime_oneHundredFiveCY_1049880536621731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 103691682173163318995821) ^ 51845841086581659497910 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 103691682173163318995821) ^ 34563894057721106331940 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 103691682173163318995821) ^ 20738336434632663799164 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 103691682173163318995821) ^ 4508334007528839956340 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 103691682173163318995821) ^ 1448835140537988780 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 103691682173163318995821) ^ 98765220 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_113063251244859843498343 : Nat.Prime 113063251244859843498343 := by
  apply lucas_primality 113063251244859843498343 (3 : ZMod 113063251244859843498343)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 7), (523, 1), (1861583, 1), (26549637637, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 7), (523, 1), (1861583, 1), (26549637637, 1)] : List FactorBlock).map factorBlockValue).prod) = 113063251244859843498343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_523
      · exact prime_oneHundredFiveCY_1861583
      · exact prime_oneHundredFiveCY_26549637637
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 113063251244859843498343) ^ 56531625622429921749171 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 37687750414953281166114 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 216182124751166048754 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 60735004157676474 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 113063251244859843498343) ^ 4258560993966 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_188581081480958316580471 : Nat.Prime 188581081480958316580471 := by
  apply lucas_primality 188581081480958316580471 (3 : ZMod 188581081480958316580471)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (2095345349788425739783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (2095345349788425739783, 1)] : List FactorBlock).map factorBlockValue).prod) = 188581081480958316580471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_2095345349788425739783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 188581081480958316580471) ^ 94290540740479158290235 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 188581081480958316580471) ^ 62860360493652772193490 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 188581081480958316580471) ^ 37716216296191663316094 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 188581081480958316580471) ^ 90 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_259193266026634557332219 : Nat.Prime 259193266026634557332219 := by
  apply lucas_primality 259193266026634557332219 (2 : ZMod 259193266026634557332219)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 3), (71, 1), (19471, 1), (273308408322643, 1)] : List FactorBlock).map factorBlockValue).prod) = 259193266026634557332219 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_71
      · exact prime_oneHundredFiveCY_19471
      · exact prime_oneHundredFiveCY_273308408322643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 259193266026634557332219) ^ 129596633013317278666109 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 37027609432376365333174 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 3650609380656824751158 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 13311759335762649958 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 259193266026634557332219) ^ 948354526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_312392005694302806360409 : Nat.Prime 312392005694302806360409 := by
  apply lucas_primality 312392005694302806360409 (7 : ZMod 312392005694302806360409)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (47, 1), (10723, 1), (170389, 1), (151576875913, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (47, 1), (10723, 1), (170389, 1), (151576875913, 1)] : List FactorBlock).map factorBlockValue).prod) = 312392005694302806360409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_47
      · exact prime_oneHundredFiveCY_10723
      · exact prime_oneHundredFiveCY_170389
      · exact prime_oneHundredFiveCY_151576875913
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 312392005694302806360409) ^ 156196002847151403180204 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 312392005694302806360409) ^ 104130668564767602120136 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 312392005694302806360409) ^ 6646638419027719284264 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 312392005694302806360409) ^ 29132892445612497096 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 312392005694302806360409) ^ 1833404771988231672 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (7 : ZMod 312392005694302806360409) ^ 2060947646616 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_452253004979439373993373 : Nat.Prime 452253004979439373993373 := by
  apply lucas_primality 452253004979439373993373 (2 : ZMod 452253004979439373993373)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113063251244859843498343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113063251244859843498343, 1)] : List FactorBlock).map factorBlockValue).prod) = 452253004979439373993373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_113063251244859843498343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 452253004979439373993373) ^ 226126502489719686996686 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 452253004979439373993373) ^ 4 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_513863111834671844657597 : Nat.Prime 513863111834671844657597 := by
  apply lucas_primality 513863111834671844657597 (2 : ZMod 513863111834671844657597)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (157, 1), (818253362794063446907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (157, 1), (818253362794063446907, 1)] : List FactorBlock).map factorBlockValue).prod) = 513863111834671844657597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_157
      · exact prime_oneHundredFiveCY_818253362794063446907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 513863111834671844657597) ^ 256931555917335922328798 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 513863111834671844657597) ^ 3273013451176253787628 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 513863111834671844657597) ^ 628 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1445785362917196837817579 : Nat.Prime 1445785362917196837817579 := by
  apply lucas_primality 1445785362917196837817579 (2 : ZMod 1445785362917196837817579)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (9926795467, 1), (2206738207199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (9926795467, 1), (2206738207199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1445785362917196837817579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_9926795467
      · exact prime_oneHundredFiveCY_2206738207199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1445785362917196837817579) ^ 722892681458598418908789 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1445785362917196837817579) ^ 481928454305732279272526 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1445785362917196837817579) ^ 131435032992472439801598 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1445785362917196837817579) ^ 145644721675134 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 1445785362917196837817579) ^ 655168500822 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2432695581547675927192243 : Nat.Prime 2432695581547675927192243 := by
  apply lucas_primality 2432695581547675927192243 (2 : ZMod 2432695581547675927192243)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (13, 1), (385042035699220627919, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (13, 1), (385042035699220627919, 1)] : List FactorBlock).map factorBlockValue).prod) = 2432695581547675927192243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_385042035699220627919
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2432695581547675927192243) ^ 1216347790773837963596121 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432695581547675927192243) ^ 810898527182558642397414 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432695581547675927192243) ^ 187130429349821225168634 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 2432695581547675927192243) ^ 6318 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_97
      · exact prime_oneHundredFiveCY_719
      · exact prime_oneHundredFiveCY_17207
      · exact prime_oneHundredFiveCY_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_5604425409968232726351827 : Nat.Prime 5604425409968232726351827 := by
  apply lucas_primality 5604425409968232726351827 (2 : ZMod 5604425409968232726351827)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) = 5604425409968232726351827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_4871
      · exact prime_oneHundredFiveCY_575284891189512700303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5604425409968232726351827) ^ 2802212704984116363175913 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 1150569782379025400606 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 9742 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_11079794968832234459897623 : Nat.Prime 11079794968832234459897623 := by
  apply lucas_primality 11079794968832234459897623 (3 : ZMod 11079794968832234459897623)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (494959, 1), (73154504292883693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (494959, 1), (73154504292883693, 1)] : List FactorBlock).map factorBlockValue).prod) = 11079794968832234459897623 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_494959
      · exact prime_oneHundredFiveCY_73154504292883693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 11079794968832234459897623) ^ 5539897484416117229948811 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11079794968832234459897623) ^ 3693264989610744819965874 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11079794968832234459897623) ^ 651752645225425556464566 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11079794968832234459897623) ^ 22385278313622410058 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 11079794968832234459897623) ^ 151457454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_12882733793150306650964401 : Nat.Prime 12882733793150306650964401 := by
  apply lucas_primality 12882733793150306650964401 (13 : ZMod 12882733793150306650964401)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (2459, 1), (64887553, 1), (67283234531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (2459, 1), (64887553, 1), (67283234531, 1)] : List FactorBlock).map factorBlockValue).prod) = 12882733793150306650964401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_2459
      · exact prime_oneHundredFiveCY_64887553
      · exact prime_oneHundredFiveCY_67283234531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 12882733793150306650964401) ^ 6441366896575153325482200 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 4294244597716768883654800 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 2576546758630061330192880 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 5239013335970031171600 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 198539368454074800 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (13 : ZMod 12882733793150306650964401) ^ 191470191392400 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_97669569497086038464746631 : Nat.Prime 97669569497086038464746631 := by
  apply lucas_primality 97669569497086038464746631 (17 : ZMod 97669569497086038464746631)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (13, 2), (57792644672831975422927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (13, 2), (57792644672831975422927, 1)] : List FactorBlock).map factorBlockValue).prod) = 97669569497086038464746631 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_57792644672831975422927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (17 : ZMod 97669569497086038464746631) ^ 48834784748543019232373315 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 97669569497086038464746631) ^ 19533913899417207692949326 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 97669569497086038464746631) ^ 7513043807468156804980510 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (17 : ZMod 97669569497086038464746631) ^ 1690 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_121823378636699072510984267 : Nat.Prime 121823378636699072510984267 := by
  apply lucas_primality 121823378636699072510984267 (2 : ZMod 121823378636699072510984267)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (19, 1), (188581081480958316580471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (19, 1), (188581081480958316580471, 1)] : List FactorBlock).map factorBlockValue).prod) = 121823378636699072510984267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_188581081480958316580471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 121823378636699072510984267) ^ 60911689318349536255492133 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 121823378636699072510984267) ^ 7166081096276416030057898 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 121823378636699072510984267) ^ 6411756770352582763736014 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 121823378636699072510984267) ^ 646 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_367272256895847203812701089 : Nat.Prime 367272256895847203812701089 := by
  apply lucas_primality 367272256895847203812701089 (3 : ZMod 367272256895847203812701089)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (13, 1), (71, 1), (73, 1), (103, 1), (6042793, 1), (273677215249, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (13, 1), (71, 1), (73, 1), (103, 1), (6042793, 1), (273677215249, 1)] : List FactorBlock).map factorBlockValue).prod) = 367272256895847203812701089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_13
      · exact prime_oneHundredFiveCY_71
      · exact prime_oneHundredFiveCY_73
      · exact prime_oneHundredFiveCY_103
      · exact prime_oneHundredFiveCY_6042793
      · exact prime_oneHundredFiveCY_273677215249
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 367272256895847203812701089) ^ 183636128447923601906350544 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 28251712068911323370207776 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 5172848688673904279052128 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 5031126806792427449489056 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 3565750066949972852550496 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 60778559996320774816 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 367272256895847203812701089) ^ 1341990624106912 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_780742281954694055903729359 : Nat.Prime 780742281954694055903729359 := by
  apply lucas_primality 780742281954694055903729359 (6 : ZMod 780742281954694055903729359)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 1), (3547, 1), (4568722909, 1), (119846578273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 1), (3547, 1), (4568722909, 1), (119846578273, 1)] : List FactorBlock).map factorBlockValue).prod) = 780742281954694055903729359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_67
      · exact prime_oneHundredFiveCY_3547
      · exact prime_oneHundredFiveCY_4568722909
      · exact prime_oneHundredFiveCY_119846578273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 780742281954694055903729359) ^ 390371140977347027951864679 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 780742281954694055903729359) ^ 260247427318231351967909786 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 780742281954694055903729359) ^ 11652869879920806804533274 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 780742281954694055903729359) ^ 220113414703888935975114 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 780742281954694055903729359) ^ 170888516880001062 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 780742281954694055903729359) ^ 6514514583605646 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_806091057342833473303201091 : Nat.Prime 806091057342833473303201091 := by
  apply lucas_primality 806091057342833473303201091 (2 : ZMod 806091057342833473303201091)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (311, 1), (259193266026634557332219, 1)] : List FactorBlock).map factorBlockValue).prod) = 806091057342833473303201091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_311
      · exact prime_oneHundredFiveCY_259193266026634557332219
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 806091057342833473303201091) ^ 403045528671416736651600545 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 161218211468566694660640218 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 2591932660266345573322190 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 806091057342833473303201091) ^ 3110 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_811359626345074214958777569 : Nat.Prime 811359626345074214958777569 := by
  apply lucas_primality 811359626345074214958777569 (3 : ZMod 811359626345074214958777569)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (61, 1), (127, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (61, 1), (127, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) = 811359626345074214958777569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_127
      · exact prime_oneHundredFiveCY_297534392471966499847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 811359626345074214958777569) ^ 405679813172537107479388784 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 73759966031370383178070688 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 13300977481066790409160288 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 6388658475158064684714784 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 811359626345074214958777569) ^ 2726944 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_977464746699183896761361953 : Nat.Prime 977464746699183896761361953 := by
  apply lucas_primality 977464746699183896761361953 (5 : ZMod 977464746699183896761361953)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 2), (11, 1), (17, 1), (61, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 2), (11, 1), (17, 1), (61, 1), (297534392471966499847, 1)] : List FactorBlock).map factorBlockValue).prod) = 977464746699183896761361953 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_61
      · exact prime_oneHundredFiveCY_297534392471966499847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 977464746699183896761361953) ^ 488732373349591948380680976 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 977464746699183896761361953) ^ 325821582233061298920453984 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 977464746699183896761361953) ^ 88860431518107626978305632 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 977464746699183896761361953) ^ 57497926276422582162433056 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 977464746699183896761361953) ^ 16024012240970227815760032 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (5 : ZMod 977464746699183896761361953) ^ 3285216 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_1241380228307963548886929681 : Nat.Prime 1241380228307963548886929681 := by
  apply lucas_primality 1241380228307963548886929681 (26 : ZMod 1241380228307963548886929681)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 1241380228307963548886929681 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_171401
      · exact prime_oneHundredFiveCY_714027719
      · exact prime_oneHundredFiveCY_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 1241380228307963548886929681) ^ 620690114153981774443464840 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 413793409435987849628976560 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 248276045661592709777385936 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 177340032615423364126704240 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 7242549508509072577680 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 1738560276128388720 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 1241380228307963548886929681) ^ 205606909308055920 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_2002226174690263788527305937 : Nat.Prime 2002226174690263788527305937 := by
  apply lucas_primality 2002226174690263788527305937 (3 : ZMod 2002226174690263788527305937)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11933, 1), (7583137, 1), (23064677, 1), (59958013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11933, 1), (7583137, 1), (23064677, 1), (59958013, 1)] : List FactorBlock).map factorBlockValue).prod) = 2002226174690263788527305937 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11933
      · exact prime_oneHundredFiveCY_7583137
      · exact prime_oneHundredFiveCY_23064677
      · exact prime_oneHundredFiveCY_59958013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2002226174690263788527305937) ^ 1001113087345131894263652968 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2002226174690263788527305937) ^ 167789003158490219435792 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2002226174690263788527305937) ^ 264036661172053701328 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2002226174690263788527305937) ^ 86809200696383642768 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 2002226174690263788527305937) ^ 33393804672784333072 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_4137934094359878496289765603 : Nat.Prime 4137934094359878496289765603 := by
  apply lucas_primality 4137934094359878496289765603 (2 : ZMod 4137934094359878496289765603)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 4137934094359878496289765603 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_4282273
      · exact prime_oneHundredFiveCY_32701811
      · exact prime_oneHundredFiveCY_343588771969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4137934094359878496289765603) ^ 2068967047179939248144882801 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 96231025450229732471855014 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 966293857108100883874 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 126535319232316476182 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 4137934094359878496289765603) ^ 12043275077490658 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_7758626426924772180543310501 : Nat.Prime 7758626426924772180543310501 := by
  apply lucas_primality 7758626426924772180543310501 (26 : ZMod 7758626426924772180543310501)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 3), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 3), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 7758626426924772180543310501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_7
      · exact prime_oneHundredFiveCY_171401
      · exact prime_oneHundredFiveCY_714027719
      · exact prime_oneHundredFiveCY_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 7758626426924772180543310501) ^ 3879313213462386090271655250 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 2586208808974924060181103500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 1551725285384954436108662100 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 1108375203846396025791901500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 45265934428181703610500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 10866001725802429500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (26 : ZMod 7758626426924772180543310501) ^ 1285043183175349500 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_20689670471799392481448828003 : Nat.Prime 20689670471799392481448828003 := by
  apply lucas_primality 20689670471799392481448828003 (2 : ZMod 20689670471799392481448828003)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) = 20689670471799392481448828003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_29
      · exact prime_oneHundredFiveCY_2663
      · exact prime_oneHundredFiveCY_31033
      · exact prime_oneHundredFiveCY_746371
      · exact prime_oneHundredFiveCY_792107
      · exact prime_oneHundredFiveCY_2433721
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20689670471799392481448828003) ^ 10344835235899696240724414001 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 6896556823933130827149609334 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 713436912820668706256856138 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 7769309227112051251013454 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 666699013044159200897394 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 27720356862471066643062 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 26119792492427654952486 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 20689670471799392481448828003) ^ 8501249926264922101362 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_24827604566159270977738593611 : Nat.Prime 24827604566159270977738593611 := by
  apply lucas_primality 24827604566159270977738593611 (2 : ZMod 24827604566159270977738593611)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270977738593611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_443
      · exact prime_oneHundredFiveCY_5604425409968232726351827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24827604566159270977738593611) ^ 12413802283079635488869296805 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4965520913231854195547718722 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 56044254099682327263518270 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4430 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_24827604566159270977738593617 : Nat.Prime 24827604566159270977738593617 := by
  apply lucas_primality 24827604566159270977738593617 (3 : ZMod 24827604566159270977738593617)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (11, 1), (19, 1), (596250997, 1), (12452009194005137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (11, 1), (19, 1), (596250997, 1), (12452009194005137, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270977738593617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_11
      · exact prime_oneHundredFiveCY_19
      · exact prime_oneHundredFiveCY_596250997
      · exact prime_oneHundredFiveCY_12452009194005137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 24827604566159270977738593617) ^ 12413802283079635488869296808 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24827604566159270977738593617) ^ 2257054960559933725248963056 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24827604566159270977738593617) ^ 1306716029797856367249399664 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24827604566159270977738593617) ^ 41639518744753178128 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 24827604566159270977738593617) ^ 1993863333968 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_31034505707699088722173242011 : Nat.Prime 31034505707699088722173242011 := by
  apply lucas_primality 31034505707699088722173242011 (2 : ZMod 31034505707699088722173242011)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) = 31034505707699088722173242011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_17
      · exact prime_oneHundredFiveCY_31969337
      · exact prime_oneHundredFiveCY_335902595973800657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 31034505707699088722173242011) ^ 15517252853849544361086621005 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31034505707699088722173242011) ^ 6206901141539817744434648402 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31034505707699088722173242011) ^ 1825559159276416983657249530 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31034505707699088722173242011) ^ 970758502364283898730 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (2 : ZMod 31034505707699088722173242011) ^ 92391383930 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_62069011415398177444346484031 : Nat.Prime 62069011415398177444346484031 := by
  apply lucas_primality 62069011415398177444346484031 (6 : ZMod 62069011415398177444346484031)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 62069011415398177444346484031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_3
      · exact prime_oneHundredFiveCY_5
      · exact prime_oneHundredFiveCY_43
      · exact prime_oneHundredFiveCY_4282273
      · exact prime_oneHundredFiveCY_32701811
      · exact prime_oneHundredFiveCY_343588771969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 62069011415398177444346484031) ^ 31034505707699088722173242015 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 20689670471799392481448828010 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 12413802283079635488869296806 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 1443465381753445987077825210 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 14494407856621513258110 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 1898029788484747142730 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (6 : ZMod 62069011415398177444346484031) ^ 180649126162359870 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiveCY_124138022830796354888692968089 : Nat.Prime 124138022830796354888692968089 := by
  apply lucas_primality 124138022830796354888692968089 (3 : ZMod 124138022830796354888692968089)
  · rw [← oneHundredFiveCYFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (2267, 1), (4349, 1), (5233, 1), (7907, 1), (146933, 1), (258876179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (2267, 1), (4349, 1), (5233, 1), (7907, 1), (146933, 1), (258876179, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiveCY_2
      · exact prime_oneHundredFiveCY_2267
      · exact prime_oneHundredFiveCY_4349
      · exact prime_oneHundredFiveCY_5233
      · exact prime_oneHundredFiveCY_7907
      · exact prime_oneHundredFiveCY_146933
      · exact prime_oneHundredFiveCY_258876179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 124138022830796354888692968089) ^ 62069011415398177444346484044 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 54758722025053531049269064 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 28544038360725765667669112 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 23722152270360472938790936 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 15699762594004850751067784 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 844861418679237168564536 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide
    · change (3 : ZMod 124138022830796354888692968089) ^ 479526634355941860872 ≠ 1
      rw [← oneHundredFiveCYFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968000 : Nat.totient 124138022830796354888692968000 = 28374239630041124513495040000 := by
  rw [← show ((([(2, 6), (3, 1), (5, 3), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968000 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_171401, prime_oneHundredFiveCY_714027719, prime_oneHundredFiveCY_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968001 : Nat.totient 124138022830796354888692968001 = 117203483396503246157695956000 := by
  rw [← show ((([(31, 1), (41, 1), (97669569497086038464746631, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968001 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_31, prime_oneHundredFiveCY_41, prime_oneHundredFiveCY_97669569497086038464746631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968002 : Nat.totient 124138022830796354888692968002 = 61371580403706768219538000608 := by
  rw [← show ((([(2, 1), (89, 1), (2325647, 1), (299875528248665142247, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968002 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_89, prime_oneHundredFiveCY_2325647, prime_oneHundredFiveCY_299875528248665142247]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968003 : Nat.totient 124138022830796354888692968003 = 74490262724750287962011256000 := by
  rw [← show ((([(3, 2), (11, 3), (101, 1), (102603667664945300223157, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968003 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_101, prime_oneHundredFiveCY_102603667664945300223157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968004 : Nat.totient 124138022830796354888692968004 = 54067246829168511634838991360 := by
  rw [← show ((([(2, 2), (13, 1), (19, 1), (269, 1), (5437, 1), (85908525773731090511, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968004 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_269, prime_oneHundredFiveCY_5437, prime_oneHundredFiveCY_85908525773731090511]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968005 : Nat.totient 124138022830796354888692968005 = 99214273384389813306542645760 := by
  rw [← show ((([(5, 1), (1321, 1), (4733, 1), (3970959864830274425357, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968005 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_1321, prime_oneHundredFiveCY_4733, prime_oneHundredFiveCY_3970959864830274425357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968006 : Nat.totient 124138022830796354888692968006 = 38887735828060237181373652992 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (677, 1), (691788953137, 1), (2598617512397, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968006 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_677, prime_oneHundredFiveCY_691788953137, prime_oneHundredFiveCY_2598617512397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968007 : Nat.totient 124138022830796354888692968007 = 101034773234870314291407403008 := by
  rw [← show ((([(7, 1), (23, 1), (137, 1), (1243169, 1), (4527184655447032079, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968007 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_23, prime_oneHundredFiveCY_137, prime_oneHundredFiveCY_1243169, prime_oneHundredFiveCY_4527184655447032079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968008 : Nat.totient 124138022830796354888692968008 = 60964770149559964166929277184 := by
  rw [← show ((([(2, 3), (59, 1), (1187, 1), (116443, 1), (205837, 1), (9244326521767, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968008 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_59, prime_oneHundredFiveCY_1187, prime_oneHundredFiveCY_116443, prime_oneHundredFiveCY_205837, prime_oneHundredFiveCY_9244326521767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968009 : Nat.totient 124138022830796354888692968009 = 81952530971887580230965657600 := by
  rw [← show ((([(3, 1), (107, 1), (3889, 1), (7297, 1), (311743, 1), (643781, 1), (67902011, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968009 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_107, prime_oneHundredFiveCY_3889, prime_oneHundredFiveCY_7297, prime_oneHundredFiveCY_311743, prime_oneHundredFiveCY_643781, prime_oneHundredFiveCY_67902011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968010 : Nat.totient 124138022830796354888692968010 = 49224398245835902355831685120 := by
  rw [← show ((([(2, 1), (5, 1), (163, 1), (617, 1), (1231, 1), (14737, 1), (22699, 1), (76163, 1), (3935629, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968010 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_163, prime_oneHundredFiveCY_617, prime_oneHundredFiveCY_1231, prime_oneHundredFiveCY_14737, prime_oneHundredFiveCY_22699, prime_oneHundredFiveCY_76163, prime_oneHundredFiveCY_3935629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968011 : Nat.totient 124138022830796354888692968011 = 124137710438790660585886210224 := by
  rw [← show ((([(397379, 1), (312392005694302806360409, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968011 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_397379, prime_oneHundredFiveCY_312392005694302806360409]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968012 : Nat.totient 124138022830796354888692968012 = 39936057044397869409662361600 := by
  rw [← show ((([(2, 2), (3, 2), (29, 1), (2663, 1), (31033, 1), (746371, 1), (792107, 1), (2433721, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968012 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_29, prime_oneHundredFiveCY_2663, prime_oneHundredFiveCY_31033, prime_oneHundredFiveCY_746371, prime_oneHundredFiveCY_792107, prime_oneHundredFiveCY_2433721]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968013 : Nat.totient 124138022830796354888692968013 = 124105622579515458761452876800 := by
  rw [← show ((([(4013, 1), (84673, 1), (222099587, 1), (1644913125451, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968013 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_4013, prime_oneHundredFiveCY_84673, prime_oneHundredFiveCY_222099587, prime_oneHundredFiveCY_1644913125451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968014 : Nat.totient 124138022830796354888692968014 = 48365463440570008398192065400 := by
  rw [← show ((([(2, 1), (7, 1), (11, 1), (806091057342833473303201091, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968014 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_806091057342833473303201091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968015 : Nat.totient 124138022830796354888692968015 = 66206945509332124502815796736 := by
  rw [← show ((([(3, 1), (5, 1), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968015 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_155440836073, prime_oneHundredFiveCY_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968016 : Nat.totient 124138022830796354888692968016 = 62069011415398177444346484000 := by
  rw [← show ((([(2, 4), (7758626426924772180543310501, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968016 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_7758626426924772180543310501]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968017 : Nat.totient 124138022830796354888692968017 = 109480221010164782883363600384 := by
  rw [← show ((([(13, 1), (43, 1), (47, 1), (1753, 1), (9319549, 1), (289213356673357, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968017 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_43, prime_oneHundredFiveCY_47, prime_oneHundredFiveCY_1753, prime_oneHundredFiveCY_9319549, prime_oneHundredFiveCY_289213356673357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968018 : Nat.totient 124138022830796354888692968018 = 41379340943598784962897656004 := by
  rw [← show ((([(2, 1), (3, 1), (20689670471799392481448828003, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968018 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_20689670471799392481448828003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968019 : Nat.totient 124138022830796354888692968019 = 124138022830788962953405173760 := by
  rw [← show ((([(16832038635521, 1), (7375103249158739, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968019 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_16832038635521, prime_oneHundredFiveCY_7375103249158739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968020 : Nat.totient 124138022830796354888692968020 = 49654731421208415316607784960 := by
  rw [← show ((([(2, 2), (5, 1), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968020 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_103981, prime_oneHundredFiveCY_292202129, prime_oneHundredFiveCY_204285462728549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968021 : Nat.totient 124138022830796354888692968021 = 70935896223879562379596473792 := by
  rw [← show ((([(3, 3), (7, 1), (607213, 1), (1081687868363620552253, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968021 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_607213, prime_oneHundredFiveCY_1081687868363620552253]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968022 : Nat.totient 124138022830796354888692968022 = 62068990851217192740608078832 := by
  rw [← show ((([(2, 1), (3018307, 1), (20564180984703735386873, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968022 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3018307, prime_oneHundredFiveCY_20564180984703735386873]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968023 : Nat.totient 124138022830796354888692968023 = 110685381174389746366829282304 := by
  rw [← show ((([(17, 1), (19, 1), (96857, 1), (10713539, 1), (370372159271287, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968023 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_96857, prime_oneHundredFiveCY_10713539, prime_oneHundredFiveCY_370372159271287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968024 : Nat.totient 124138022830796354888692968024 = 41375722919558949447905617536 := by
  rw [← show ((([(2, 3), (3, 1), (11437, 1), (452253004979439373993373, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968024 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_11437, prime_oneHundredFiveCY_452253004979439373993373]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968025 : Nat.totient 124138022830796354888692968025 = 90242408996755505572652640000 := by
  rw [← show ((([(5, 2), (11, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968025 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_2269, prime_oneHundredFiveCY_24570248051, prime_oneHundredFiveCY_8097073720069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968026 : Nat.totient 124138022830796354888692968026 = 61051486637853489170064756480 := by
  rw [← show ((([(2, 1), (61, 1), (251174804057, 1), (4051062291545369, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968026 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_61, prime_oneHundredFiveCY_251174804057, prime_oneHundredFiveCY_4051062291545369]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968027 : Nat.totient 124138022830796354888692968027 = 82280308003324854508271113632 := by
  rw [← show ((([(3, 1), (173, 1), (625830854527, 1), (382191034750579, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968027 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_173, prime_oneHundredFiveCY_625830854527, prime_oneHundredFiveCY_382191034750579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968028 : Nat.totient 124138022830796354888692968028 = 51070164965190394969549094400 := by
  rw [← show ((([(2, 2), (7, 1), (53, 1), (71, 1), (131, 1), (8993759679696815118617, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968028 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_53, prime_oneHundredFiveCY_71, prime_oneHundredFiveCY_131, prime_oneHundredFiveCY_8993759679696815118617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968029 : Nat.totient 124138022830796354888692968029 = 123484570261261856073204839040 := by
  rw [← show ((([(191, 1), (35129, 1), (58221874103, 1), (317774825437, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968029 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_191, prime_oneHundredFiveCY_35129, prime_oneHundredFiveCY_58221874103, prime_oneHundredFiveCY_317774825437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968030 : Nat.totient 124138022830796354888692968030 = 29228484305311248776468170752 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968030 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_23, prime_oneHundredFiveCY_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968031 : Nat.totient 124138022830796354888692968031 = 123160558084097170991931605952 := by
  rw [← show ((([(127, 1), (977464746699183896761361953, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968031 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_127, prime_oneHundredFiveCY_977464746699183896761361953]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968032 : Nat.totient 124138022830796354888692968032 = 60061740044389674269946347520 := by
  rw [← show ((([(2, 5), (31, 1), (11933, 1), (7583137, 1), (23064677, 1), (59958013, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968032 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_31, prime_oneHundredFiveCY_11933, prime_oneHundredFiveCY_7583137, prime_oneHundredFiveCY_23064677, prime_oneHundredFiveCY_59958013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968033 : Nat.totient 124138022830796354888692968033 = 82738025703275020073676902400 := by
  rw [← show ((([(3, 1), (4153, 1), (113537, 1), (87757496123468850851, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968033 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_4153, prime_oneHundredFiveCY_113537, prime_oneHundredFiveCY_87757496123468850851]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968034 : Nat.totient 124138022830796354888692968034 = 62012563072272340152626182272 := by
  rw [← show ((([(2, 1), (1193, 1), (14029, 1), (1389262187, 1), (2669460224903, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968034 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_1193, prime_oneHundredFiveCY_14029, prime_oneHundredFiveCY_1389262187, prime_oneHundredFiveCY_2669460224903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968035 : Nat.totient 124138022830796354888692968035 = 82819931676784100601026153472 := by
  rw [← show ((([(5, 1), (7, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968035 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_37, prime_oneHundredFiveCY_31177, prime_oneHundredFiveCY_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968036 : Nat.totient 124138022830796354888692968036 = 37102273324272883154777472000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (73, 1), (12882733793150306650964401, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968036 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_73, prime_oneHundredFiveCY_12882733793150306650964401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968037 : Nat.totient 124138022830796354888692968037 = 122988449610557785965234009600 := by
  rw [← show ((([(109, 1), (13109, 1), (96281, 1), (3834907, 1), (235295344231, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968037 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_109, prime_oneHundredFiveCY_13109, prime_oneHundredFiveCY_96281, prime_oneHundredFiveCY_3834907, prime_oneHundredFiveCY_235295344231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968038 : Nat.totient 124138022830796354888692968038 = 61833007337245580024312458056 := by
  rw [← show ((([(2, 1), (263, 1), (265986547, 1), (887277376798777079, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968038 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_263, prime_oneHundredFiveCY_265986547, prime_oneHundredFiveCY_887277376798777079]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968039 : Nat.totient 124138022830796354888692968039 = 82679218395433485247035694080 := by
  rw [← show ((([(3, 2), (1069, 1), (43711, 1), (594023, 1), (5539187, 1), (89710769, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968039 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_1069, prime_oneHundredFiveCY_43711, prime_oneHundredFiveCY_594023, prime_oneHundredFiveCY_5539187, prime_oneHundredFiveCY_89710769]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968040 : Nat.totient 124138022830796354888692968040 = 46734313015628176964514578432 := by
  rw [← show ((([(2, 3), (5, 1), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968040 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_31969337, prime_oneHundredFiveCY_335902595973800657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968041 : Nat.totient 124138022830796354888692968041 = 119740009006306077226428774400 := by
  rw [← show ((([(29, 1), (1049, 1), (39551, 1), (1128977, 1), (91387916234123, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968041 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_29, prime_oneHundredFiveCY_1049, prime_oneHundredFiveCY_39551, prime_oneHundredFiveCY_1128977, prime_oneHundredFiveCY_91387916234123]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968042 : Nat.totient 124138022830796354888692968042 = 32699150164305384760348508160 := by
  rw [← show ((([(2, 1), (3, 1), (7, 2), (19, 1), (41, 1), (397, 1), (13617913, 1), (100257985466497, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968042 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_41, prime_oneHundredFiveCY_397, prime_oneHundredFiveCY_13617913, prime_oneHundredFiveCY_100257985466497]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968043 : Nat.totient 124138022830796354888692968043 = 114588095990968355857858676736 := by
  rw [← show ((([(13, 1), (135119, 1), (1133535457, 1), (62346193038617, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968043 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_135119, prime_oneHundredFiveCY_1133535457, prime_oneHundredFiveCY_62346193038617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968044 : Nat.totient 124138022830796354888692968044 = 62069011415398177444346484020 := by
  rw [← show ((([(2, 2), (31034505707699088722173242011, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968044 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_31034505707699088722173242011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968045 : Nat.totient 124138022830796354888692968045 = 66206943610464788295843111104 := by
  rw [← show ((([(3, 1), (5, 1), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968045 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_34858727, prime_oneHundredFiveCY_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968046 : Nat.totient 124138022830796354888692968046 = 61694908519591546571101480800 := by
  rw [← show ((([(2, 1), (179, 1), (2381, 1), (43271, 1), (3365623024283972887, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968046 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_179, prime_oneHundredFiveCY_2381, prime_oneHundredFiveCY_43271, prime_oneHundredFiveCY_3365623024283972887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968047 : Nat.totient 124138022830796354888692968047 = 112828421072181209503176183960 := by
  rw [← show ((([(11, 1), (4639, 1), (2432695581547675927192243, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968047 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_4639, prime_oneHundredFiveCY_2432695581547675927192243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968048 : Nat.totient 124138022830796354888692968048 = 41310490125031956507809894400 := by
  rw [← show ((([(2, 4), (3, 5), (601, 1), (24740943389, 1), (2147275852489, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968048 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_601, prime_oneHundredFiveCY_24740943389, prime_oneHundredFiveCY_2147275852489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968049 : Nat.totient 124138022830796354888692968049 = 106310592715413396052017907200 := by
  rw [← show ((([(7, 1), (1697, 1), (3461, 1), (3019418713742564280571, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968049 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_1697, prime_oneHundredFiveCY_3461, prime_oneHundredFiveCY_3019418713742564280571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968050 : Nat.totient 124138022830796354888692968050 = 49543120624119177300950141840 := by
  rw [← show ((([(2, 1), (5, 2), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968050 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_443, prime_oneHundredFiveCY_5604425409968232726351827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968051 : Nat.totient 124138022830796354888692968051 = 82758675780409734138582533600 := by
  rw [← show ((([(3, 1), (13551917, 1), (3053393917893592837301, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968051 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_13551917, prime_oneHundredFiveCY_3053393917893592837301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968052 : Nat.totient 124138022830796354888692968052 = 61030884415134318572832030720 := by
  rw [← show ((([(2, 2), (181, 1), (193, 1), (223, 2), (919, 1), (1823, 1), (10663432953857, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968052 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_181, prime_oneHundredFiveCY_193, prime_oneHundredFiveCY_223, prime_oneHundredFiveCY_919, prime_oneHundredFiveCY_1823, prime_oneHundredFiveCY_10663432953857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968053 : Nat.totient 124138022830796354888692968053 = 117545178690217452624721108992 := by
  rw [← show ((([(23, 1), (103, 1), (2753, 1), (32105053, 1), (592870936031993, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968053 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_23, prime_oneHundredFiveCY_103, prime_oneHundredFiveCY_2753, prime_oneHundredFiveCY_32105053, prime_oneHundredFiveCY_592870936031993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968054 : Nat.totient 124138022830796354888692968054 = 41379340943580926567263479432 := by
  rw [← show ((([(2, 1), (3, 1), (2317682119507, 1), (8926880134968787, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968054 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_2317682119507, prime_oneHundredFiveCY_8926880134968787]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968055 : Nat.totient 124138022830796354888692968055 = 99310418264637083910954374440 := by
  rw [← show ((([(5, 1), (24827604566159270977738593611, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968055 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_24827604566159270977738593611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968056 : Nat.totient 124138022830796354888692968056 = 48360795918978929800939531776 := by
  rw [← show ((([(2, 3), (7, 1), (13, 1), (67, 1), (3067, 1), (829821849978416232493, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968056 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_67, prime_oneHundredFiveCY_3067, prime_oneHundredFiveCY_829821849978416232493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968057 : Nat.totient 124138022830796354888692968057 = 77890524129127124636042646528 := by
  rw [← show ((([(3, 2), (17, 1), (811359626345074214958777569, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968057 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_811359626345074214958777569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968058 : Nat.totient 124138022830796354888692968058 = 56373190055430131895137481600 := by
  rw [← show ((([(2, 1), (11, 1), (1061, 1), (33117977, 1), (160584254210685187, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968058 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_1061, prime_oneHundredFiveCY_33117977, prime_oneHundredFiveCY_160584254210685187]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968059 : Nat.totient 124138022830796354888692968059 = 124138022730532155296440969320 := by
  rw [← show ((([(1238109149, 1), (100264199591013889591, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968059 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_1238109149, prime_oneHundredFiveCY_100264199591013889591]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968060 : Nat.totient 124138022830796354888692968060 = 32333616011866960775742750720 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968060 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_43, prime_oneHundredFiveCY_4282273, prime_oneHundredFiveCY_32701811, prime_oneHundredFiveCY_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968061 : Nat.totient 124138022830796354888692968061 = 117599199270353183337141882240 := by
  rw [← show ((([(19, 1), (24571, 1), (257273, 1), (1033556399581327493, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968061 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_24571, prime_oneHundredFiveCY_257273, prime_oneHundredFiveCY_1033556399581327493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968062 : Nat.totient 124138022830796354888692968062 = 62069011415398177444346484030 := by
  rw [← show ((([(2, 1), (62069011415398177444346484031, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968062 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_62069011415398177444346484031]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968063 : Nat.totient 124138022830796354888692968063 = 68647735486737664858464353280 := by
  rw [← show ((([(3, 1), (7, 1), (31, 1), (3599009, 1), (52983531609217552957, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968063 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_31, prime_oneHundredFiveCY_3599009, prime_oneHundredFiveCY_52983531609217552957]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968064 : Nat.totient 124138022830796354888692968064 = 60443125838922976602491427840 := by
  rw [← show ((([(2, 7), (47, 1), (199, 1), (103691682173163318995821, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968064 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_47, prime_oneHundredFiveCY_199, prime_oneHundredFiveCY_103691682173163318995821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968065 : Nat.totient 124138022830796354888692968065 = 99310074747481630483301602752 := by
  rw [← show ((([(5, 1), (289103, 1), (20288258719, 1), (4232894525309, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968065 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_289103, prime_oneHundredFiveCY_20288258719, prime_oneHundredFiveCY_4232894525309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968066 : Nat.totient 124138022830796354888692968066 = 41376257764927776931829629920 := by
  rw [← show ((([(2, 1), (3, 2), (13421, 1), (513863111834671844657597, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968066 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_13421, prime_oneHundredFiveCY_513863111834671844657597]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968067 : Nat.totient 124138022830796354888692968067 = 120547660377569987928127198848 := by
  rw [← show ((([(59, 1), (83, 1), (7517, 1), (350415259, 1), (9623812659437, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968067 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_59, prime_oneHundredFiveCY_83, prime_oneHundredFiveCY_7517, prime_oneHundredFiveCY_350415259, prime_oneHundredFiveCY_9623812659437]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968068 : Nat.totient 124138022830796354888692968068 = 61954812522981233567962790400 := by
  rw [← show ((([(2, 2), (1373, 1), (1549, 1), (2141, 1), (6815633209915294781, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968068 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_1373, prime_oneHundredFiveCY_1549, prime_oneHundredFiveCY_2141, prime_oneHundredFiveCY_6815633209915294781]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968069 : Nat.totient 124138022830796354888692968069 = 69043290899290044600556800000 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1), (251, 1), (541, 1), (6039193, 1), (352856105336047, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968069 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_251, prime_oneHundredFiveCY_541, prime_oneHundredFiveCY_6039193, prime_oneHundredFiveCY_352856105336047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968070 : Nat.totient 124138022830796354888692968070 = 40639589391783839901740040192 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968070 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_29, prime_oneHundredFiveCY_113, prime_oneHundredFiveCY_449, prime_oneHundredFiveCY_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968071 : Nat.totient 124138022830796354888692968071 = 123824929496857495962669065088 := by
  rw [← show ((([(487, 1), (2129, 1), (89151479, 1), (1342986505854263, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968071 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_487, prime_oneHundredFiveCY_2129, prime_oneHundredFiveCY_89151479, prime_oneHundredFiveCY_1342986505854263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968072 : Nat.totient 124138022830796354888692968072 = 40253580748446014687496192000 := by
  rw [← show ((([(2, 3), (3, 1), (37, 1), (5441, 1), (545363909, 1), (47111478990451, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968072 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_37, prime_oneHundredFiveCY_5441, prime_oneHundredFiveCY_545363909, prime_oneHundredFiveCY_47111478990451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968073 : Nat.totient 124138022830796354888692968073 = 124016199452159655816181982788 := by
  rw [← show ((([(1019, 1), (121823378636699072510984267, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968073 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_1019, prime_oneHundredFiveCY_121823378636699072510984267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968074 : Nat.totient 124138022830796354888692968074 = 57435830887793404590625536000 := by
  rw [← show ((([(2, 1), (17, 1), (79, 1), (239, 1), (45481, 1), (4251781223518704301, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968074 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_79, prime_oneHundredFiveCY_239, prime_oneHundredFiveCY_45481, prime_oneHundredFiveCY_4251781223518704301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968075 : Nat.totient 124138022830796354888692968075 = 66206498657710401874578816000 := by
  rw [← show ((([(3, 3), (5, 2), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968075 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_148193, prime_oneHundredFiveCY_732506743, prime_oneHundredFiveCY_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968076 : Nat.totient 124138022830796354888692968076 = 59356730973818673446743137600 := by
  rw [← show ((([(2, 2), (23, 1), (4363, 1), (2956061, 1), (104620885602558571, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968076 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_23, prime_oneHundredFiveCY_4363, prime_oneHundredFiveCY_2956061, prime_oneHundredFiveCY_104620885602558571]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968077 : Nat.totient 124138022830796354888692968077 = 106027043363723070400063530240 := by
  rw [← show ((([(7, 1), (283, 1), (107071, 1), (11129533489, 1), (52586168543, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968077 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_283, prime_oneHundredFiveCY_107071, prime_oneHundredFiveCY_11129533489, prime_oneHundredFiveCY_52586168543]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968078 : Nat.totient 124138022830796354888692968078 = 41379340943597870886373428480 := by
  rw [← show ((([(2, 1), (3, 1), (50948517533153, 1), (406089744580621, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968078 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_50948517533153, prime_oneHundredFiveCY_406089744580621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968079 : Nat.totient 124138022830796354888692968079 = 123294408719404689659444428800 := by
  rw [← show ((([(151, 1), (7673, 1), (24223, 1), (735479, 1), (755137, 1), (7964137, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968079 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_151, prime_oneHundredFiveCY_7673, prime_oneHundredFiveCY_24223, prime_oneHundredFiveCY_735479, prime_oneHundredFiveCY_755137, prime_oneHundredFiveCY_7964137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968080 : Nat.totient 124138022830796354888692968080 = 42765251812569904718105026560 := by
  rw [← show ((([(2, 4), (5, 1), (11, 1), (19, 1), (596250997, 1), (12452009194005137, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968080 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_596250997, prime_oneHundredFiveCY_12452009194005137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968081 : Nat.totient 124138022830796354888692968081 = 81197197323288181813987853232 := by
  rw [← show ((([(3, 1), (53, 1), (780742281954694055903729359, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968081 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_53, prime_oneHundredFiveCY_780742281954694055903729359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968082 : Nat.totient 124138022830796354888692968082 = 57294472075752163794781369728 := by
  rw [← show ((([(2, 1), (13, 2), (367272256895847203812701089, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968082 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_367272256895847203812701089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968083 : Nat.totient 124138022830796354888692968083 = 120679268787303313769499417600 := by
  rw [← show ((([(41, 1), (281, 1), (218280729577, 1), (49362739139099, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968083 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_41, prime_oneHundredFiveCY_281, prime_oneHundredFiveCY_218280729577, prime_oneHundredFiveCY_49362739139099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968084 : Nat.totient 124138022830796354888692968084 = 35460967594062388797891521280 := by
  rw [← show ((([(2, 2), (3, 2), (7, 1), (5879, 1), (35267, 1), (88812211, 1), (26752207429, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968084 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_5879, prime_oneHundredFiveCY_35267, prime_oneHundredFiveCY_88812211, prime_oneHundredFiveCY_26752207429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968085 : Nat.totient 124138022830796354888692968085 = 99310418264637083910954374464 := by
  rw [← show ((([(5, 1), (24827604566159270977738593617, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968085 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_24827604566159270977738593617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968086 : Nat.totient 124138022830796354888692968086 = 61429113333918937543181596416 := by
  rw [← show ((([(2, 1), (97, 1), (5451263, 1), (635013539, 1), (184851497767, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968086 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_97, prime_oneHundredFiveCY_5451263, prime_oneHundredFiveCY_635013539, prime_oneHundredFiveCY_184851497767]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968087 : Nat.totient 124138022830796354888692968087 = 81401410673438228221897850880 := by
  rw [← show ((([(3, 1), (61, 1), (142433, 1), (4762589087742351216833, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968087 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_61, prime_oneHundredFiveCY_142433, prime_oneHundredFiveCY_4762589087742351216833]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968088 : Nat.totient 124138022830796354888692968088 = 62007247844666049408658120704 := by
  rw [← show ((([(2, 3), (2267, 1), (4349, 1), (5233, 1), (7907, 1), (146933, 1), (258876179, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968088 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_2267, prime_oneHundredFiveCY_4349, prime_oneHundredFiveCY_5233, prime_oneHundredFiveCY_7907, prime_oneHundredFiveCY_146933, prime_oneHundredFiveCY_258876179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968089 : Nat.totient 124138022830796354888692968089 = 124138022830796354888692968088 := by
  rw [← show ((([(124138022830796354888692968089, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968089 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_124138022830796354888692968089]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968090 : Nat.totient 124138022830796354888692968090 = 33103472754879027970318124816 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (4137934094359878496289765603, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968090 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_4137934094359878496289765603]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968091 : Nat.totient 124138022830796354888692968091 = 89230161774619297971044352000 := by
  rw [← show ((([(7, 3), (11, 1), (17, 1), (89, 1), (139, 1), (673, 1), (12101, 1), (19210026562297, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968091 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_11, prime_oneHundredFiveCY_17, prime_oneHundredFiveCY_89, prime_oneHundredFiveCY_139, prime_oneHundredFiveCY_673, prime_oneHundredFiveCY_12101, prime_oneHundredFiveCY_19210026562297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968092 : Nat.totient 124138022830796354888692968092 = 62046851825460512975426683200 := by
  rw [← show ((([(2, 2), (2801, 1), (11079794968832234459897623, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968092 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_2801, prime_oneHundredFiveCY_11079794968832234459897623]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968093 : Nat.totient 124138022830796354888692968093 = 82436663658817779805080766464 := by
  rw [← show ((([(3, 2), (257, 1), (7549237799, 1), (7109287631275139, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968093 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_257, prime_oneHundredFiveCY_7549237799, prime_oneHundredFiveCY_7109287631275139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968094 : Nat.totient 124138022830796354888692968094 = 60066785240707913655819178080 := by
  rw [← show ((([(2, 1), (31, 1), (2002226174690263788527305937, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968094 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_31, prime_oneHundredFiveCY_2002226174690263788527305937]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968095 : Nat.totient 124138022830796354888692968095 = 91073261559626410147448924160 := by
  rw [← show ((([(5, 1), (13, 1), (167, 2), (1861, 1), (160346779, 1), (229483735993, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968095 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_13, prime_oneHundredFiveCY_167, prime_oneHundredFiveCY_1861, prime_oneHundredFiveCY_160346779, prime_oneHundredFiveCY_229483735993]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968096 : Nat.totient 124138022830796354888692968096 = 41375115920123650059701739264 := by
  rw [← show ((([(2, 5), (3, 1), (9803, 1), (10517539, 1), (12541816931536903, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968096 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_9803, prime_oneHundredFiveCY_10517539, prime_oneHundredFiveCY_12541816931536903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968097 : Nat.totient 124138022830796354888692968097 = 124107010914715845227916970560 := by
  rw [← show ((([(4003, 1), (185564411, 1), (167118506749901009, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968097 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_4003, prime_oneHundredFiveCY_185564411, prime_oneHundredFiveCY_167118506749901009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968098 : Nat.totient 124138022830796354888692968098 = 53193335072449506056984329776 := by
  rw [← show ((([(2, 1), (7, 1), (6133, 1), (1445785362917196837817579, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968098 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_7, prime_oneHundredFiveCY_6133, prime_oneHundredFiveCY_1445785362917196837817579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968099 : Nat.totient 124138022830796354888692968099 = 71267277965816706423180410880 := by
  rw [← show ((([(3, 1), (19, 1), (23, 1), (29, 2), (71, 1), (599, 1), (38677, 1), (68449169782753, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968099 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_3, prime_oneHundredFiveCY_19, prime_oneHundredFiveCY_23, prime_oneHundredFiveCY_29, prime_oneHundredFiveCY_71, prime_oneHundredFiveCY_599, prime_oneHundredFiveCY_38677, prime_oneHundredFiveCY_68449169782753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968100 : Nat.totient 124138022830796354888692968100 = 49655209132318541955477187200 := by
  rw [← show ((([(2, 2), (5, 2), (1241380228307963548886929681, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968100 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_2, prime_oneHundredFiveCY_5, prime_oneHundredFiveCY_1241380228307963548886929681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiveCY_124138022830796354888692968101 : Nat.totient 124138022830796354888692968101 = 124128561812158977929988106240 := by
  rw [← show ((([(13121, 1), (625819384877, 1), (15117809801753, 1)] : List FactorBlock).map factorBlockValue).prod) = 124138022830796354888692968101 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiveCY_13121, prime_oneHundredFiveCY_625819384877, prime_oneHundredFiveCY_15117809801753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiveCY : certifiedKill 1 124138022830796354888692967999 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiveCY_124138022830796354888692968000, phi_oneHundredFiveCY_124138022830796354888692968001, phi_oneHundredFiveCY_124138022830796354888692968002,
    phi_oneHundredFiveCY_124138022830796354888692968003, phi_oneHundredFiveCY_124138022830796354888692968004, phi_oneHundredFiveCY_124138022830796354888692968005,
    phi_oneHundredFiveCY_124138022830796354888692968006, phi_oneHundredFiveCY_124138022830796354888692968007, phi_oneHundredFiveCY_124138022830796354888692968008,
    phi_oneHundredFiveCY_124138022830796354888692968009, phi_oneHundredFiveCY_124138022830796354888692968010, phi_oneHundredFiveCY_124138022830796354888692968011,
    phi_oneHundredFiveCY_124138022830796354888692968012, phi_oneHundredFiveCY_124138022830796354888692968013, phi_oneHundredFiveCY_124138022830796354888692968014,
    phi_oneHundredFiveCY_124138022830796354888692968015, phi_oneHundredFiveCY_124138022830796354888692968016, phi_oneHundredFiveCY_124138022830796354888692968017,
    phi_oneHundredFiveCY_124138022830796354888692968018, phi_oneHundredFiveCY_124138022830796354888692968019, phi_oneHundredFiveCY_124138022830796354888692968020,
    phi_oneHundredFiveCY_124138022830796354888692968021, phi_oneHundredFiveCY_124138022830796354888692968022, phi_oneHundredFiveCY_124138022830796354888692968023,
    phi_oneHundredFiveCY_124138022830796354888692968024, phi_oneHundredFiveCY_124138022830796354888692968025, phi_oneHundredFiveCY_124138022830796354888692968026,
    phi_oneHundredFiveCY_124138022830796354888692968027, phi_oneHundredFiveCY_124138022830796354888692968028, phi_oneHundredFiveCY_124138022830796354888692968029,
    phi_oneHundredFiveCY_124138022830796354888692968030, phi_oneHundredFiveCY_124138022830796354888692968031, phi_oneHundredFiveCY_124138022830796354888692968032,
    phi_oneHundredFiveCY_124138022830796354888692968033, phi_oneHundredFiveCY_124138022830796354888692968034, phi_oneHundredFiveCY_124138022830796354888692968035,
    phi_oneHundredFiveCY_124138022830796354888692968036, phi_oneHundredFiveCY_124138022830796354888692968037, phi_oneHundredFiveCY_124138022830796354888692968038,
    phi_oneHundredFiveCY_124138022830796354888692968039, phi_oneHundredFiveCY_124138022830796354888692968040, phi_oneHundredFiveCY_124138022830796354888692968041,
    phi_oneHundredFiveCY_124138022830796354888692968042, phi_oneHundredFiveCY_124138022830796354888692968043, phi_oneHundredFiveCY_124138022830796354888692968044,
    phi_oneHundredFiveCY_124138022830796354888692968045, phi_oneHundredFiveCY_124138022830796354888692968046, phi_oneHundredFiveCY_124138022830796354888692968047,
    phi_oneHundredFiveCY_124138022830796354888692968048, phi_oneHundredFiveCY_124138022830796354888692968049, phi_oneHundredFiveCY_124138022830796354888692968050,
    phi_oneHundredFiveCY_124138022830796354888692968051, phi_oneHundredFiveCY_124138022830796354888692968052, phi_oneHundredFiveCY_124138022830796354888692968053,
    phi_oneHundredFiveCY_124138022830796354888692968054, phi_oneHundredFiveCY_124138022830796354888692968055, phi_oneHundredFiveCY_124138022830796354888692968056,
    phi_oneHundredFiveCY_124138022830796354888692968057, phi_oneHundredFiveCY_124138022830796354888692968058, phi_oneHundredFiveCY_124138022830796354888692968059,
    phi_oneHundredFiveCY_124138022830796354888692968060, phi_oneHundredFiveCY_124138022830796354888692968061, phi_oneHundredFiveCY_124138022830796354888692968062,
    phi_oneHundredFiveCY_124138022830796354888692968063, phi_oneHundredFiveCY_124138022830796354888692968064, phi_oneHundredFiveCY_124138022830796354888692968065,
    phi_oneHundredFiveCY_124138022830796354888692968066, phi_oneHundredFiveCY_124138022830796354888692968067, phi_oneHundredFiveCY_124138022830796354888692968068,
    phi_oneHundredFiveCY_124138022830796354888692968069, phi_oneHundredFiveCY_124138022830796354888692968070, phi_oneHundredFiveCY_124138022830796354888692968071,
    phi_oneHundredFiveCY_124138022830796354888692968072, phi_oneHundredFiveCY_124138022830796354888692968073, phi_oneHundredFiveCY_124138022830796354888692968074,
    phi_oneHundredFiveCY_124138022830796354888692968075, phi_oneHundredFiveCY_124138022830796354888692968076, phi_oneHundredFiveCY_124138022830796354888692968077,
    phi_oneHundredFiveCY_124138022830796354888692968078, phi_oneHundredFiveCY_124138022830796354888692968079, phi_oneHundredFiveCY_124138022830796354888692968080,
    phi_oneHundredFiveCY_124138022830796354888692968081, phi_oneHundredFiveCY_124138022830796354888692968082, phi_oneHundredFiveCY_124138022830796354888692968083,
    phi_oneHundredFiveCY_124138022830796354888692968084, phi_oneHundredFiveCY_124138022830796354888692968085, phi_oneHundredFiveCY_124138022830796354888692968086,
    phi_oneHundredFiveCY_124138022830796354888692968087, phi_oneHundredFiveCY_124138022830796354888692968088, phi_oneHundredFiveCY_124138022830796354888692968089,
    phi_oneHundredFiveCY_124138022830796354888692968090, phi_oneHundredFiveCY_124138022830796354888692968091, phi_oneHundredFiveCY_124138022830796354888692968092,
    phi_oneHundredFiveCY_124138022830796354888692968093, phi_oneHundredFiveCY_124138022830796354888692968094, phi_oneHundredFiveCY_124138022830796354888692968095,
    phi_oneHundredFiveCY_124138022830796354888692968096, phi_oneHundredFiveCY_124138022830796354888692968097, phi_oneHundredFiveCY_124138022830796354888692968098,
    phi_oneHundredFiveCY_124138022830796354888692968099, phi_oneHundredFiveCY_124138022830796354888692968100, phi_oneHundredFiveCY_124138022830796354888692968101
    ]

end TotientTailPeriodKiller
end Erdos249257
