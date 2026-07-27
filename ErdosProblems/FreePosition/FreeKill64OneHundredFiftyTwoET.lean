import Erdos249257.DiagonalPincerCertificatesT64
/- Kernel-checked off-diagonal certificate at a freely chosen position. -/
namespace Erdos249257
namespace TotientTailPeriodKiller
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
private def oneHundredFiftyTwoETFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredFiftyTwoETFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredFiftyTwoETFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredFiftyTwoETFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredFiftyTwoETFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredFiftyTwoETFastPow a n * oneHundredFiftyTwoETFastPow a n * a else oneHundredFiftyTwoETFastPow a n * oneHundredFiftyTwoETFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredFiftyTwoET_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredFiftyTwoET_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredFiftyTwoET_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredFiftyTwoET_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredFiftyTwoET_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredFiftyTwoET_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredFiftyTwoET_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredFiftyTwoET_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredFiftyTwoET_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredFiftyTwoET_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredFiftyTwoET_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredFiftyTwoET_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredFiftyTwoET_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredFiftyTwoET_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredFiftyTwoET_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredFiftyTwoET_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredFiftyTwoET_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredFiftyTwoET_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredFiftyTwoET_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredFiftyTwoET_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredFiftyTwoET_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredFiftyTwoET_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredFiftyTwoET_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredFiftyTwoET_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredFiftyTwoET_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredFiftyTwoET_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredFiftyTwoET_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredFiftyTwoET_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredFiftyTwoET_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredFiftyTwoET_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredFiftyTwoET_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredFiftyTwoET_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredFiftyTwoET_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredFiftyTwoET_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredFiftyTwoET_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredFiftyTwoET_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredFiftyTwoET_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredFiftyTwoET_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredFiftyTwoET_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredFiftyTwoET_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredFiftyTwoET_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredFiftyTwoET_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredFiftyTwoET_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredFiftyTwoET_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredFiftyTwoET_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredFiftyTwoET_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredFiftyTwoET_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredFiftyTwoET_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredFiftyTwoET_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredFiftyTwoET_257 : Nat.Prime 257 := by norm_num

private theorem prime_oneHundredFiftyTwoET_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredFiftyTwoET_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredFiftyTwoET_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredFiftyTwoET_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredFiftyTwoET_281 : Nat.Prime 281 := by norm_num

private theorem prime_oneHundredFiftyTwoET_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredFiftyTwoET_307 : Nat.Prime 307 := by norm_num

private theorem prime_oneHundredFiftyTwoET_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredFiftyTwoET_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredFiftyTwoET_337 : Nat.Prime 337 := by norm_num

private theorem prime_oneHundredFiftyTwoET_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredFiftyTwoET_349 : Nat.Prime 349 := by norm_num

private theorem prime_oneHundredFiftyTwoET_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredFiftyTwoET_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredFiftyTwoET_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredFiftyTwoET_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredFiftyTwoET_383 : Nat.Prime 383 := by norm_num

private theorem prime_oneHundredFiftyTwoET_389 : Nat.Prime 389 := by norm_num

private theorem prime_oneHundredFiftyTwoET_409 : Nat.Prime 409 := by norm_num

private theorem prime_oneHundredFiftyTwoET_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredFiftyTwoET_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredFiftyTwoET_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredFiftyTwoET_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredFiftyTwoET_479 : Nat.Prime 479 := by norm_num

private theorem prime_oneHundredFiftyTwoET_491 : Nat.Prime 491 := by norm_num

private theorem prime_oneHundredFiftyTwoET_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredFiftyTwoET_509 : Nat.Prime 509 := by norm_num

private theorem prime_oneHundredFiftyTwoET_541 : Nat.Prime 541 := by norm_num

private theorem prime_oneHundredFiftyTwoET_563 : Nat.Prime 563 := by norm_num

private theorem prime_oneHundredFiftyTwoET_571 : Nat.Prime 571 := by norm_num

private theorem prime_oneHundredFiftyTwoET_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredFiftyTwoET_653 : Nat.Prime 653 := by norm_num

private theorem prime_oneHundredFiftyTwoET_659 : Nat.Prime 659 := by norm_num

private theorem prime_oneHundredFiftyTwoET_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredFiftyTwoET_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredFiftyTwoET_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredFiftyTwoET_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredFiftyTwoET_751 : Nat.Prime 751 := by norm_num

private theorem prime_oneHundredFiftyTwoET_769 : Nat.Prime 769 := by norm_num

private theorem prime_oneHundredFiftyTwoET_787 : Nat.Prime 787 := by norm_num

private theorem prime_oneHundredFiftyTwoET_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredFiftyTwoET_809 : Nat.Prime 809 := by norm_num

private theorem prime_oneHundredFiftyTwoET_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredFiftyTwoET_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredFiftyTwoET_839 : Nat.Prime 839 := by norm_num

private theorem prime_oneHundredFiftyTwoET_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredFiftyTwoET_919 : Nat.Prime 919 := by norm_num

private theorem prime_oneHundredFiftyTwoET_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1019 : Nat.Prime 1019 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1061 : Nat.Prime 1061 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1069 : Nat.Prime 1069 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1117 : Nat.Prime 1117 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1279 : Nat.Prime 1279 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1303 : Nat.Prime 1303 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1319 : Nat.Prime 1319 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1367 : Nat.Prime 1367 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1433 : Nat.Prime 1433 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1459 : Nat.Prime 1459 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1487 : Nat.Prime 1487 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1493 : Nat.Prime 1493 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1571 : Nat.Prime 1571 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1609 : Nat.Prime 1609 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1637 : Nat.Prime 1637 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1693 : Nat.Prime 1693 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1723 : Nat.Prime 1723 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1753 : Nat.Prime 1753 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1789 : Nat.Prime 1789 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1801 : Nat.Prime 1801 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1823 : Nat.Prime 1823 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1931 : Nat.Prime 1931 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1951 : Nat.Prime 1951 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2053 : Nat.Prime 2053 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2213 : Nat.Prime 2213 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2243 : Nat.Prime 2243 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2251 : Nat.Prime 2251 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2383 : Nat.Prime 2383 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2549 : Nat.Prime 2549 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2677 : Nat.Prime 2677 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2819 : Nat.Prime 2819 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3049 : Nat.Prime 3049 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3121 : Nat.Prime 3121 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3221 : Nat.Prime 3221 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3301 : Nat.Prime 3301 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3347 : Nat.Prime 3347 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3511 : Nat.Prime 3511 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3529 : Nat.Prime 3529 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3547 : Nat.Prime 3547 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3581 : Nat.Prime 3581 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3623 : Nat.Prime 3623 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3701 : Nat.Prime 3701 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3767 : Nat.Prime 3767 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3881 : Nat.Prime 3881 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3923 : Nat.Prime 3923 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4177 : Nat.Prime 4177 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4219 : Nat.Prime 4219 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4337 : Nat.Prime 4337 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4423 : Nat.Prime 4423 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4481 : Nat.Prime 4481 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4493 : Nat.Prime 4493 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4561 : Nat.Prime 4561 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4783 : Nat.Prime 4783 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4801 : Nat.Prime 4801 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5051 : Nat.Prime 5051 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5087 : Nat.Prime 5087 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5527 : Nat.Prime 5527 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5647 : Nat.Prime 5647 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5717 : Nat.Prime 5717 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5903 : Nat.Prime 5903 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6197 : Nat.Prime 6197 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6763 : Nat.Prime 6763 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6823 : Nat.Prime 6823 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6827 : Nat.Prime 6827 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6911 : Nat.Prime 6911 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6959 : Nat.Prime 6959 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7001 : Nat.Prime 7001 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7069 : Nat.Prime 7069 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7207 : Nat.Prime 7207 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7561 : Nat.Prime 7561 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7817 : Nat.Prime 7817 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7951 : Nat.Prime 7951 := by norm_num

private theorem prime_oneHundredFiftyTwoET_8167 : Nat.Prime 8167 := by norm_num

private theorem prime_oneHundredFiftyTwoET_8219 : Nat.Prime 8219 := by norm_num

private theorem prime_oneHundredFiftyTwoET_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredFiftyTwoET_8747 : Nat.Prime 8747 := by norm_num

private theorem prime_oneHundredFiftyTwoET_8779 : Nat.Prime 8779 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9013 : Nat.Prime 9013 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9091 : Nat.Prime 9091 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9341 : Nat.Prime 9341 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9787 : Nat.Prime 9787 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9811 : Nat.Prime 9811 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9887 : Nat.Prime 9887 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9949 : Nat.Prime 9949 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10729 : Nat.Prime 10729 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10789 : Nat.Prime 10789 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10847 : Nat.Prime 10847 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10957 : Nat.Prime 10957 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11437 : Nat.Prime 11437 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11491 : Nat.Prime 11491 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11887 : Nat.Prime 11887 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11897 : Nat.Prime 11897 := by norm_num

private theorem prime_oneHundredFiftyTwoET_12479 : Nat.Prime 12479 := by norm_num

private theorem prime_oneHundredFiftyTwoET_12553 : Nat.Prime 12553 := by norm_num

private theorem prime_oneHundredFiftyTwoET_13399 : Nat.Prime 13399 := by norm_num

private theorem prime_oneHundredFiftyTwoET_13903 : Nat.Prime 13903 := by norm_num

private theorem prime_oneHundredFiftyTwoET_14251 : Nat.Prime 14251 := by norm_num

private theorem prime_oneHundredFiftyTwoET_14633 : Nat.Prime 14633 := by norm_num

private theorem prime_oneHundredFiftyTwoET_14653 : Nat.Prime 14653 := by norm_num

private theorem prime_oneHundredFiftyTwoET_14699 : Nat.Prime 14699 := by norm_num

private theorem prime_oneHundredFiftyTwoET_15233 : Nat.Prime 15233 := by norm_num

private theorem prime_oneHundredFiftyTwoET_15451 : Nat.Prime 15451 := by norm_num

private theorem prime_oneHundredFiftyTwoET_15733 : Nat.Prime 15733 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16007 : Nat.Prime 16007 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16223 : Nat.Prime 16223 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16333 : Nat.Prime 16333 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16901 : Nat.Prime 16901 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16943 : Nat.Prime 16943 := by norm_num

private theorem prime_oneHundredFiftyTwoET_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredFiftyTwoET_17443 : Nat.Prime 17443 := by norm_num

private theorem prime_oneHundredFiftyTwoET_18583 : Nat.Prime 18583 := by norm_num

private theorem prime_oneHundredFiftyTwoET_19309 : Nat.Prime 19309 := by norm_num

private theorem prime_oneHundredFiftyTwoET_19403 : Nat.Prime 19403 := by norm_num

private theorem prime_oneHundredFiftyTwoET_19423 : Nat.Prime 19423 := by norm_num

private theorem prime_oneHundredFiftyTwoET_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredFiftyTwoET_21227 : Nat.Prime 21227 := by norm_num

private theorem prime_oneHundredFiftyTwoET_22039 : Nat.Prime 22039 := by norm_num

private theorem prime_oneHundredFiftyTwoET_22807 : Nat.Prime 22807 := by norm_num

private theorem prime_oneHundredFiftyTwoET_22859 : Nat.Prime 22859 := by norm_num

private theorem prime_oneHundredFiftyTwoET_24841 : Nat.Prime 24841 := by norm_num

private theorem prime_oneHundredFiftyTwoET_24889 : Nat.Prime 24889 := by norm_num

private theorem prime_oneHundredFiftyTwoET_26227 : Nat.Prime 26227 := by norm_num

private theorem prime_oneHundredFiftyTwoET_27241 : Nat.Prime 27241 := by norm_num

private theorem prime_oneHundredFiftyTwoET_29297 : Nat.Prime 29297 := by norm_num

private theorem prime_oneHundredFiftyTwoET_30713 : Nat.Prime 30713 := by norm_num

private theorem prime_oneHundredFiftyTwoET_30853 : Nat.Prime 30853 := by norm_num

private theorem prime_oneHundredFiftyTwoET_32603 : Nat.Prime 32603 := by norm_num

private theorem prime_oneHundredFiftyTwoET_32969 : Nat.Prime 32969 := by norm_num

private theorem prime_oneHundredFiftyTwoET_33457 : Nat.Prime 33457 := by norm_num

private theorem prime_oneHundredFiftyTwoET_34283 : Nat.Prime 34283 := by norm_num

private theorem prime_oneHundredFiftyTwoET_35353 : Nat.Prime 35353 := by norm_num

private theorem prime_oneHundredFiftyTwoET_35759 : Nat.Prime 35759 := by norm_num

private theorem prime_oneHundredFiftyTwoET_37619 : Nat.Prime 37619 := by norm_num

private theorem prime_oneHundredFiftyTwoET_38351 : Nat.Prime 38351 := by norm_num

private theorem prime_oneHundredFiftyTwoET_40771 : Nat.Prime 40771 := by norm_num

private theorem prime_oneHundredFiftyTwoET_44059 : Nat.Prime 44059 := by norm_num

private theorem prime_oneHundredFiftyTwoET_44753 : Nat.Prime 44753 := by norm_num

private theorem prime_oneHundredFiftyTwoET_46187 : Nat.Prime 46187 := by norm_num

private theorem prime_oneHundredFiftyTwoET_46327 : Nat.Prime 46327 := by norm_num

private theorem prime_oneHundredFiftyTwoET_46477 : Nat.Prime 46477 := by norm_num

private theorem prime_oneHundredFiftyTwoET_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredFiftyTwoET_49529 : Nat.Prime 49529 := by norm_num

private theorem prime_oneHundredFiftyTwoET_49667 : Nat.Prime 49667 := by norm_num

private theorem prime_oneHundredFiftyTwoET_49741 : Nat.Prime 49741 := by norm_num

private theorem prime_oneHundredFiftyTwoET_52127 : Nat.Prime 52127 := by norm_num

private theorem prime_oneHundredFiftyTwoET_52147 : Nat.Prime 52147 := by norm_num

private theorem prime_oneHundredFiftyTwoET_52919 : Nat.Prime 52919 := by norm_num

private theorem prime_oneHundredFiftyTwoET_54437 : Nat.Prime 54437 := by norm_num

private theorem prime_oneHundredFiftyTwoET_54833 : Nat.Prime 54833 := by norm_num

private theorem prime_oneHundredFiftyTwoET_57737 : Nat.Prime 57737 := by norm_num

private theorem prime_oneHundredFiftyTwoET_60257 : Nat.Prime 60257 := by norm_num

private theorem prime_oneHundredFiftyTwoET_60821 : Nat.Prime 60821 := by norm_num

private theorem prime_oneHundredFiftyTwoET_62653 : Nat.Prime 62653 := by norm_num

private theorem prime_oneHundredFiftyTwoET_68521 : Nat.Prime 68521 := by norm_num

private theorem prime_oneHundredFiftyTwoET_68767 : Nat.Prime 68767 := by norm_num

private theorem prime_oneHundredFiftyTwoET_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredFiftyTwoET_72953 : Nat.Prime 72953 := by norm_num

private theorem prime_oneHundredFiftyTwoET_74197 : Nat.Prime 74197 := by norm_num

private theorem prime_oneHundredFiftyTwoET_76511 : Nat.Prime 76511 := by norm_num

private theorem prime_oneHundredFiftyTwoET_76801 : Nat.Prime 76801 := by norm_num

private theorem prime_oneHundredFiftyTwoET_77291 : Nat.Prime 77291 := by norm_num

private theorem prime_oneHundredFiftyTwoET_78233 : Nat.Prime 78233 := by norm_num

private theorem prime_oneHundredFiftyTwoET_78691 : Nat.Prime 78691 := by norm_num

private theorem prime_oneHundredFiftyTwoET_79967 : Nat.Prime 79967 := by norm_num

private theorem prime_oneHundredFiftyTwoET_80341 : Nat.Prime 80341 := by norm_num

private theorem prime_oneHundredFiftyTwoET_80473 : Nat.Prime 80473 := by norm_num

private theorem prime_oneHundredFiftyTwoET_80621 : Nat.Prime 80621 := by norm_num

private theorem prime_oneHundredFiftyTwoET_80923 : Nat.Prime 80923 := by norm_num

private theorem prime_oneHundredFiftyTwoET_85733 : Nat.Prime 85733 := by norm_num

private theorem prime_oneHundredFiftyTwoET_89597 : Nat.Prime 89597 := by norm_num

private theorem prime_oneHundredFiftyTwoET_91243 : Nat.Prime 91243 := by norm_num

private theorem prime_oneHundredFiftyTwoET_96589 : Nat.Prime 96589 := by norm_num

private theorem prime_oneHundredFiftyTwoET_97169 : Nat.Prime 97169 := by norm_num

private theorem prime_oneHundredFiftyTwoET_99529 : Nat.Prime 99529 := by norm_num

private theorem prime_oneHundredFiftyTwoET_99907 : Nat.Prime 99907 := by norm_num

private theorem prime_oneHundredFiftyTwoET_104113 : Nat.Prime 104113 := by norm_num

private theorem prime_oneHundredFiftyTwoET_106391 : Nat.Prime 106391 := by norm_num

private theorem prime_oneHundredFiftyTwoET_114773 : Nat.Prime 114773 := by norm_num

private theorem prime_oneHundredFiftyTwoET_116747 : Nat.Prime 116747 := by norm_num

private theorem prime_oneHundredFiftyTwoET_120557 : Nat.Prime 120557 := by norm_num

private theorem prime_oneHundredFiftyTwoET_123143 : Nat.Prime 123143 := by norm_num

private theorem prime_oneHundredFiftyTwoET_125471 : Nat.Prime 125471 := by norm_num

private theorem prime_oneHundredFiftyTwoET_128389 : Nat.Prime 128389 := by norm_num

private theorem prime_oneHundredFiftyTwoET_128483 : Nat.Prime 128483 := by norm_num

private theorem prime_oneHundredFiftyTwoET_137453 : Nat.Prime 137453 := by norm_num

private theorem prime_oneHundredFiftyTwoET_138319 : Nat.Prime 138319 := by norm_num

private theorem prime_oneHundredFiftyTwoET_139303 : Nat.Prime 139303 := by norm_num

private theorem prime_oneHundredFiftyTwoET_142969 : Nat.Prime 142969 := by norm_num

private theorem prime_oneHundredFiftyTwoET_143141 : Nat.Prime 143141 := by norm_num

private theorem prime_oneHundredFiftyTwoET_145219 : Nat.Prime 145219 := by norm_num

private theorem prime_oneHundredFiftyTwoET_156593 : Nat.Prime 156593 := by norm_num

private theorem prime_oneHundredFiftyTwoET_160883 : Nat.Prime 160883 := by norm_num

private theorem prime_oneHundredFiftyTwoET_168629 : Nat.Prime 168629 := by norm_num

private theorem prime_oneHundredFiftyTwoET_170603 : Nat.Prime 170603 := by norm_num

private theorem prime_oneHundredFiftyTwoET_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredFiftyTwoET_192667 : Nat.Prime 192667 := by norm_num

private theorem prime_oneHundredFiftyTwoET_201451 : Nat.Prime 201451 := by norm_num

private theorem prime_oneHundredFiftyTwoET_211427 : Nat.Prime 211427 := by norm_num

private theorem prime_oneHundredFiftyTwoET_214807 : Nat.Prime 214807 := by norm_num

private theorem prime_oneHundredFiftyTwoET_232171 : Nat.Prime 232171 := by norm_num

private theorem prime_oneHundredFiftyTwoET_240893 : Nat.Prime 240893 := by norm_num

private theorem prime_oneHundredFiftyTwoET_242647 : Nat.Prime 242647 := by norm_num

private theorem prime_oneHundredFiftyTwoET_244423 : Nat.Prime 244423 := by norm_num

private theorem prime_oneHundredFiftyTwoET_245299 : Nat.Prime 245299 := by norm_num

private theorem prime_oneHundredFiftyTwoET_245513 : Nat.Prime 245513 := by norm_num

private theorem prime_oneHundredFiftyTwoET_248371 : Nat.Prime 248371 := by norm_num

private theorem prime_oneHundredFiftyTwoET_253651 : Nat.Prime 253651 := by norm_num

private theorem prime_oneHundredFiftyTwoET_259201 : Nat.Prime 259201 := by norm_num

private theorem prime_oneHundredFiftyTwoET_271969 : Nat.Prime 271969 := by norm_num

private theorem prime_oneHundredFiftyTwoET_274199 : Nat.Prime 274199 := by norm_num

private theorem prime_oneHundredFiftyTwoET_283277 : Nat.Prime 283277 := by norm_num

private theorem prime_oneHundredFiftyTwoET_285317 : Nat.Prime 285317 := by norm_num

private theorem prime_oneHundredFiftyTwoET_290869 : Nat.Prime 290869 := by norm_num

private theorem prime_oneHundredFiftyTwoET_299099 : Nat.Prime 299099 := by norm_num

private theorem prime_oneHundredFiftyTwoET_299281 : Nat.Prime 299281 := by norm_num

private theorem prime_oneHundredFiftyTwoET_317599 : Nat.Prime 317599 := by norm_num

private theorem prime_oneHundredFiftyTwoET_324199 : Nat.Prime 324199 := by norm_num

private theorem prime_oneHundredFiftyTwoET_324361 : Nat.Prime 324361 := by norm_num

private theorem prime_oneHundredFiftyTwoET_324503 : Nat.Prime 324503 := by norm_num

private theorem prime_oneHundredFiftyTwoET_325709 : Nat.Prime 325709 := by norm_num

private theorem prime_oneHundredFiftyTwoET_345769 : Nat.Prime 345769 := by norm_num

private theorem prime_oneHundredFiftyTwoET_352333 : Nat.Prime 352333 := by norm_num

private theorem prime_oneHundredFiftyTwoET_355087 : Nat.Prime 355087 := by norm_num

private theorem prime_oneHundredFiftyTwoET_358279 : Nat.Prime 358279 := by norm_num

private theorem prime_oneHundredFiftyTwoET_360007 : Nat.Prime 360007 := by norm_num

private theorem prime_oneHundredFiftyTwoET_362027 : Nat.Prime 362027 := by norm_num

private theorem prime_oneHundredFiftyTwoET_364759 : Nat.Prime 364759 := by norm_num

private theorem prime_oneHundredFiftyTwoET_370511 : Nat.Prime 370511 := by norm_num

private theorem prime_oneHundredFiftyTwoET_378011 : Nat.Prime 378011 := by norm_num

private theorem prime_oneHundredFiftyTwoET_379177 : Nat.Prime 379177 := by norm_num

private theorem prime_oneHundredFiftyTwoET_379681 : Nat.Prime 379681 := by norm_num

private theorem prime_oneHundredFiftyTwoET_390989 : Nat.Prime 390989 := by norm_num

private theorem prime_oneHundredFiftyTwoET_418337 : Nat.Prime 418337 := by norm_num

private theorem prime_oneHundredFiftyTwoET_425653 : Nat.Prime 425653 := by norm_num

private theorem prime_oneHundredFiftyTwoET_427327 : Nat.Prime 427327 := by norm_num

private theorem prime_oneHundredFiftyTwoET_470501 : Nat.Prime 470501 := by norm_num

private theorem prime_oneHundredFiftyTwoET_471589 : Nat.Prime 471589 := by norm_num

private theorem prime_oneHundredFiftyTwoET_510199 : Nat.Prime 510199 := by norm_num

private theorem prime_oneHundredFiftyTwoET_534253 : Nat.Prime 534253 := by norm_num

private theorem prime_oneHundredFiftyTwoET_536447 : Nat.Prime 536447 := by norm_num

private theorem prime_oneHundredFiftyTwoET_593519 : Nat.Prime 593519 := by norm_num

private theorem prime_oneHundredFiftyTwoET_594119 : Nat.Prime 594119 := by norm_num

private theorem prime_oneHundredFiftyTwoET_718841 : Nat.Prime 718841 := by norm_num

private theorem prime_oneHundredFiftyTwoET_764209 : Nat.Prime 764209 := by norm_num

private theorem prime_oneHundredFiftyTwoET_799291 : Nat.Prime 799291 := by norm_num

private theorem prime_oneHundredFiftyTwoET_801607 : Nat.Prime 801607 := by norm_num

private theorem prime_oneHundredFiftyTwoET_827581 : Nat.Prime 827581 := by norm_num

private theorem prime_oneHundredFiftyTwoET_837667 : Nat.Prime 837667 := by norm_num

private theorem prime_oneHundredFiftyTwoET_873043 : Nat.Prime 873043 := by norm_num

private theorem prime_oneHundredFiftyTwoET_881983 : Nat.Prime 881983 := by norm_num

private theorem prime_oneHundredFiftyTwoET_885589 : Nat.Prime 885589 := by norm_num

private theorem prime_oneHundredFiftyTwoET_888661 : Nat.Prime 888661 := by norm_num

private theorem prime_oneHundredFiftyTwoET_902477 : Nat.Prime 902477 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1039517 : Nat.Prime 1039517 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1178711 : Nat.Prime 1178711 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1201729 : Nat.Prime 1201729 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1273421 : Nat.Prime 1273421 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1293367 : Nat.Prime 1293367 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1381967 : Nat.Prime 1381967 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1387849 : Nat.Prime 1387849 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1391587 : Nat.Prime 1391587 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1496927 : Nat.Prime 1496927 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1506257 : Nat.Prime 1506257 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1565569 : Nat.Prime 1565569 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1592653 : Nat.Prime 1592653 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1657231 : Nat.Prime 1657231 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1695131 : Nat.Prime 1695131 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1703297 : Nat.Prime 1703297 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1809937 : Nat.Prime 1809937 := by norm_num

private theorem prime_oneHundredFiftyTwoET_1910429 : Nat.Prime 1910429 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2191067 : Nat.Prime 2191067 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2275657 : Nat.Prime 2275657 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2426107 : Nat.Prime 2426107 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2515757 : Nat.Prime 2515757 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2606267 : Nat.Prime 2606267 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2692093 : Nat.Prime 2692093 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2755243 : Nat.Prime 2755243 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2804693 : Nat.Prime 2804693 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2857949 : Nat.Prime 2857949 := by norm_num

private theorem prime_oneHundredFiftyTwoET_2977717 : Nat.Prime 2977717 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3042997 : Nat.Prime 3042997 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3159001 : Nat.Prime 3159001 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3594403 : Nat.Prime 3594403 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3695257 : Nat.Prime 3695257 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3824993 : Nat.Prime 3824993 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3851359 : Nat.Prime 3851359 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3852697 : Nat.Prime 3852697 := by norm_num

private theorem prime_oneHundredFiftyTwoET_3880889 : Nat.Prime 3880889 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4440187 : Nat.Prime 4440187 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4556179 : Nat.Prime 4556179 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4932311 : Nat.Prime 4932311 := by norm_num

private theorem prime_oneHundredFiftyTwoET_4994357 : Nat.Prime 4994357 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5005223 : Nat.Prime 5005223 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5316797 : Nat.Prime 5316797 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5578421 : Nat.Prime 5578421 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5699467 : Nat.Prime 5699467 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5743987 : Nat.Prime 5743987 := by norm_num

private theorem prime_oneHundredFiftyTwoET_5867033 : Nat.Prime 5867033 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6134851 : Nat.Prime 6134851 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6208691 : Nat.Prime 6208691 := by norm_num

private theorem prime_oneHundredFiftyTwoET_6977483 : Nat.Prime 6977483 := by norm_num

private theorem prime_oneHundredFiftyTwoET_7156783 : Nat.Prime 7156783 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9130651 : Nat.Prime 9130651 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9694877 : Nat.Prime 9694877 := by norm_num

private theorem prime_oneHundredFiftyTwoET_9733489 : Nat.Prime 9733489 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10233161 : Nat.Prime 10233161 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10655581 : Nat.Prime 10655581 := by norm_num

private theorem prime_oneHundredFiftyTwoET_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11164369 : Nat.Prime 11164369 := by norm_num

private theorem prime_oneHundredFiftyTwoET_11484661 : Nat.Prime 11484661 := by norm_num

private theorem prime_oneHundredFiftyTwoET_12456349 : Nat.Prime 12456349 := by norm_num

private theorem prime_oneHundredFiftyTwoET_12807317 : Nat.Prime 12807317 := by norm_num

private theorem prime_oneHundredFiftyTwoET_14581213 : Nat.Prime 14581213 := by norm_num

private theorem prime_oneHundredFiftyTwoET_16185671 : Nat.Prime 16185671 := by norm_num

private theorem prime_oneHundredFiftyTwoET_17002049 : Nat.Prime 17002049 := by norm_num

private theorem prime_oneHundredFiftyTwoET_18547603 : Nat.Prime 18547603 := by norm_num

private theorem prime_oneHundredFiftyTwoET_19112231 : Nat.Prime 19112231 := by norm_num

private theorem prime_oneHundredFiftyTwoET_20291147 : Nat.Prime 20291147 := by norm_num

private theorem prime_oneHundredFiftyTwoET_20637977 : Nat.Prime 20637977 := by norm_num

private theorem prime_oneHundredFiftyTwoET_21739801 : Nat.Prime 21739801 := by norm_num

private theorem prime_oneHundredFiftyTwoET_21971737 : Nat.Prime 21971737 := by norm_num

private theorem prime_oneHundredFiftyTwoET_23121181 : Nat.Prime 23121181 := by norm_num

private theorem prime_oneHundredFiftyTwoET_23217409 : Nat.Prime 23217409 := by norm_num

private theorem prime_oneHundredFiftyTwoET_23983727 : Nat.Prime 23983727 := by norm_num

private theorem prime_oneHundredFiftyTwoET_26080009 : Nat.Prime 26080009 := by norm_num

private theorem prime_oneHundredFiftyTwoET_26732501 : Nat.Prime 26732501 := by norm_num

private theorem prime_oneHundredFiftyTwoET_27528119 : Nat.Prime 27528119 := by norm_num

private theorem prime_oneHundredFiftyTwoET_28581281 : Nat.Prime 28581281 := by norm_num

private theorem prime_oneHundredFiftyTwoET_28901293 : Nat.Prime 28901293 := by norm_num

private theorem prime_oneHundredFiftyTwoET_31238257 : Nat.Prime 31238257 := by
  apply lucas_primality 31238257 (5 : ZMod 31238257)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (239, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (239, 1), (389, 1)] : List FactorBlock).map factorBlockValue).prod) = 31238257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_239
      · exact prime_oneHundredFiftyTwoET_389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 31238257) ^ 15619128 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 31238257) ^ 10412752 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 31238257) ^ 4462608 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 31238257) ^ 130704 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 31238257) ^ 80304 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_32371343 : Nat.Prime 32371343 := by
  apply lucas_primality 32371343 (5 : ZMod 32371343)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (16185671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (16185671, 1)] : List FactorBlock).map factorBlockValue).prod) = 32371343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_16185671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 32371343) ^ 16185671 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 32371343) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_37872883 : Nat.Prime 37872883 := by
  apply lucas_primality 37872883 (3 : ZMod 37872883)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (47, 1), (89, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (47, 1), (89, 1), (503, 1)] : List FactorBlock).map factorBlockValue).prod) = 37872883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_47
      · exact prime_oneHundredFiftyTwoET_89
      · exact prime_oneHundredFiftyTwoET_503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37872883) ^ 18936441 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37872883) ^ 12624294 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37872883) ^ 805806 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37872883) ^ 425538 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37872883) ^ 75294 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_39182089 : Nat.Prime 39182089 := by
  apply lucas_primality 39182089 (29 : ZMod 39182089)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (193, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (193, 1), (769, 1)] : List FactorBlock).map factorBlockValue).prod) = 39182089 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_193
      · exact prime_oneHundredFiftyTwoET_769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (29 : ZMod 39182089) ^ 19591044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (29 : ZMod 39182089) ^ 13060696 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (29 : ZMod 39182089) ^ 3562008 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (29 : ZMod 39182089) ^ 203016 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (29 : ZMod 39182089) ^ 50952 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_39221387 : Nat.Prime 39221387 := by
  apply lucas_primality 39221387 (2 : ZMod 39221387)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (31, 1), (163, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (31, 1), (163, 1), (3881, 1)] : List FactorBlock).map factorBlockValue).prod) = 39221387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_31
      · exact prime_oneHundredFiftyTwoET_163
      · exact prime_oneHundredFiftyTwoET_3881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39221387) ^ 19610693 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39221387) ^ 1265206 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39221387) ^ 240622 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39221387) ^ 10106 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_39544963 : Nat.Prime 39544963 := by
  apply lucas_primality 39544963 (2 : ZMod 39544963)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (389, 1), (16943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (389, 1), (16943, 1)] : List FactorBlock).map factorBlockValue).prod) = 39544963 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_389
      · exact prime_oneHundredFiftyTwoET_16943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 39544963) ^ 19772481 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39544963) ^ 13181654 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39544963) ^ 101658 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 39544963) ^ 2334 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_43170289 : Nat.Prime 43170289 := by
  apply lucas_primality 43170289 (11 : ZMod 43170289)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (128483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (128483, 1)] : List FactorBlock).map factorBlockValue).prod) = 43170289 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_128483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 43170289) ^ 21585144 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 43170289) ^ 14390096 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 43170289) ^ 6167184 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 43170289) ^ 336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_44967817 : Nat.Prime 44967817 := by
  apply lucas_primality 44967817 (10 : ZMod 44967817)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (41, 1), (15233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (41, 1), (15233, 1)] : List FactorBlock).map factorBlockValue).prod) = 44967817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_41
      · exact prime_oneHundredFiftyTwoET_15233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 44967817) ^ 22483908 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 44967817) ^ 14989272 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 44967817) ^ 1096776 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 44967817) ^ 2952 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_48219551 : Nat.Prime 48219551 := by
  apply lucas_primality 48219551 (7 : ZMod 48219551)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (107, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (107, 1), (9013, 1)] : List FactorBlock).map factorBlockValue).prod) = 48219551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_107
      · exact prime_oneHundredFiftyTwoET_9013
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 48219551) ^ 24109775 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 48219551) ^ 9643910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 48219551) ^ 450650 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 48219551) ^ 5350 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_52514747 : Nat.Prime 52514747 := by
  apply lucas_primality 52514747 (2 : ZMod 52514747)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1381967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1381967, 1)] : List FactorBlock).map factorBlockValue).prod) = 52514747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_1381967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 52514747) ^ 26257373 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 52514747) ^ 2763934 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 52514747) ^ 38 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_53321713 : Nat.Prime 53321713 := by
  apply lucas_primality 53321713 (5 : ZMod 53321713)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (127, 1), (8747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (127, 1), (8747, 1)] : List FactorBlock).map factorBlockValue).prod) = 53321713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_127
      · exact prime_oneHundredFiftyTwoET_8747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 53321713) ^ 26660856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 53321713) ^ 17773904 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 53321713) ^ 419856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 53321713) ^ 6096 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_56069599 : Nat.Prime 56069599 := by
  apply lucas_primality 56069599 (15 : ZMod 56069599)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (718841, 1)] : List FactorBlock).map factorBlockValue).prod) = 56069599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_718841
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (15 : ZMod 56069599) ^ 28034799 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 18689866 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 4313046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 56069599) ^ 78 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_58148407 : Nat.Prime 58148407 := by
  apply lucas_primality 58148407 (3 : ZMod 58148407)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (719, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (719, 1), (4493, 1)] : List FactorBlock).map factorBlockValue).prod) = 58148407 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_719
      · exact prime_oneHundredFiftyTwoET_4493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58148407) ^ 29074203 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 58148407) ^ 19382802 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 58148407) ^ 80874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 58148407) ^ 12942 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1811
      · exact prime_oneHundredFiftyTwoET_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_61132733 : Nat.Prime 61132733 := by
  apply lucas_primality 61132733 (2 : ZMod 61132733)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (37, 1), (59, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (37, 1), (59, 1), (7001, 1)] : List FactorBlock).map factorBlockValue).prod) = 61132733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_37
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_7001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 61132733) ^ 30566366 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61132733) ^ 1652236 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61132733) ^ 1036148 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61132733) ^ 8732 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_62146589 : Nat.Prime 62146589 := by
  apply lucas_primality 62146589 (2 : ZMod 62146589)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (59, 1), (37619, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (59, 1), (37619, 1)] : List FactorBlock).map factorBlockValue).prod) = 62146589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_37619
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 62146589) ^ 31073294 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 62146589) ^ 8878084 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 62146589) ^ 1053332 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 62146589) ^ 1652 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_64742687 : Nat.Prime 64742687 := by
  apply lucas_primality 64742687 (5 : ZMod 64742687)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (32371343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (32371343, 1)] : List FactorBlock).map factorBlockValue).prod) = 64742687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_32371343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 64742687) ^ 32371343 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 64742687) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_66708619 : Nat.Prime 66708619 := by
  apply lucas_primality 66708619 (3 : ZMod 66708619)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (71, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (71, 1), (156593, 1)] : List FactorBlock).map factorBlockValue).prod) = 66708619 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_156593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 66708619) ^ 33354309 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 22236206 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 939558 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 66708619) ^ 426 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_72794101 : Nat.Prime 72794101 := by
  apply lucas_primality 72794101 (6 : ZMod 72794101)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (242647, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (242647, 1)] : List FactorBlock).map factorBlockValue).prod) = 72794101 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_242647
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 72794101) ^ 36397050 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 72794101) ^ 24264700 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 72794101) ^ 14558820 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 72794101) ^ 300 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_72827129 : Nat.Prime 72827129 := by
  apply lucas_primality 72827129 (3 : ZMod 72827129)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (827581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (827581, 1)] : List FactorBlock).map factorBlockValue).prod) = 72827129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_827581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 72827129) ^ 36413564 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 72827129) ^ 6620648 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 72827129) ^ 88 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_76449433 : Nat.Prime 76449433 := by
  apply lucas_primality 76449433 (5 : ZMod 76449433)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (199, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (199, 1), (16007, 1)] : List FactorBlock).map factorBlockValue).prod) = 76449433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_199
      · exact prime_oneHundredFiftyTwoET_16007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 76449433) ^ 38224716 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 25483144 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 384168 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 76449433) ^ 4776 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_79883233 : Nat.Prime 79883233 := by
  apply lucas_primality 79883233 (7 : ZMod 79883233)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 2), (13, 1), (23, 2)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 2), (13, 1), (23, 2)] : List FactorBlock).map factorBlockValue).prod) = 79883233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_23
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 79883233) ^ 39941616 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 79883233) ^ 26627744 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 79883233) ^ 7262112 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 79883233) ^ 6144864 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 79883233) ^ 3473184 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_91454369 : Nat.Prime 91454369 := by
  apply lucas_primality 91454369 (3 : ZMod 91454369)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (2857949, 1)] : List FactorBlock).map factorBlockValue).prod) = 91454369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_2857949
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 91454369) ^ 45727184 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 91454369) ^ 32 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_91776389 : Nat.Prime 91776389 := by
  apply lucas_primality 91776389 (2 : ZMod 91776389)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (59, 1), (35353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (59, 1), (35353, 1)] : List FactorBlock).map factorBlockValue).prod) = 91776389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_35353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 91776389) ^ 45888194 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 91776389) ^ 8343308 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 91776389) ^ 1555532 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 91776389) ^ 2596 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_92103133 : Nat.Prime 92103133 := by
  apply lucas_primality 92103133 (5 : ZMod 92103133)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (23, 2), (1319, 1)] : List FactorBlock).map factorBlockValue).prod) = 92103133 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_1319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 92103133) ^ 46051566 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 30701044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 8373012 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 4004484 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 92103133) ^ 69828 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_99479969 : Nat.Prime 99479969 := by
  apply lucas_primality 99479969 (6 : ZMod 99479969)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (23, 1), (19309, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (23, 1), (19309, 1)] : List FactorBlock).map factorBlockValue).prod) = 99479969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_19309
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 99479969) ^ 49739984 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 99479969) ^ 14211424 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 99479969) ^ 4325216 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 99479969) ^ 5152 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_101080961 : Nat.Prime 101080961 := by
  apply lucas_primality 101080961 (3 : ZMod 101080961)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (5, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 101080961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 101080961) ^ 50540480 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 20216192 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 2350720 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 101080961) ^ 27520 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_102534983 : Nat.Prime 102534983 := by
  apply lucas_primality 102534983 (5 : ZMod 102534983)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (245299, 1)] : List FactorBlock).map factorBlockValue).prod) = 102534983 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_245299
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 102534983) ^ 51267491 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 9321362 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 5396578 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 102534983) ^ 418 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_104320037 : Nat.Prime 104320037 := by
  apply lucas_primality 104320037 (2 : ZMod 104320037)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (26080009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (26080009, 1)] : List FactorBlock).map factorBlockValue).prod) = 104320037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_26080009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 104320037) ^ 52160018 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 104320037) ^ 4 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_115461013 : Nat.Prime 115461013 := by
  apply lucas_primality 115461013 (11 : ZMod 115461013)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (23, 1), (418337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (23, 1), (418337, 1)] : List FactorBlock).map factorBlockValue).prod) = 115461013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_418337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 115461013) ^ 57730506 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 115461013) ^ 38487004 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 115461013) ^ 5020044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 115461013) ^ 276 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_125476717 : Nat.Prime 125476717 := by
  apply lucas_primality 125476717 (6 : ZMod 125476717)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (31, 1), (59, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (31, 1), (59, 1), (5717, 1)] : List FactorBlock).map factorBlockValue).prod) = 125476717 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_31
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_5717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 125476717) ^ 62738358 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 125476717) ^ 41825572 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 125476717) ^ 4047636 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 125476717) ^ 2126724 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 125476717) ^ 21948 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_125933891 : Nat.Prime 125933891 := by
  apply lucas_primality 125933891 (2 : ZMod 125933891)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (61, 1), (431, 1), (479, 1)] : List FactorBlock).map factorBlockValue).prod) = 125933891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_61
      · exact prime_oneHundredFiftyTwoET_431
      · exact prime_oneHundredFiftyTwoET_479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 125933891) ^ 62966945 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 25186778 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 2064490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 292190 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 125933891) ^ 262910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_133972429 : Nat.Prime 133972429 := by
  apply lucas_primality 133972429 (2 : ZMod 133972429)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11164369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11164369, 1)] : List FactorBlock).map factorBlockValue).prod) = 133972429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11164369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 133972429) ^ 66986214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 133972429) ^ 44657476 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 133972429) ^ 12 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_138727087 : Nat.Prime 138727087 := by
  apply lucas_primality 138727087 (3 : ZMod 138727087)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23121181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23121181, 1)] : List FactorBlock).map factorBlockValue).prod) = 138727087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_23121181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 138727087) ^ 69363543 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 138727087) ^ 46242362 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 138727087) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_140084323 : Nat.Prime 140084323 := by
  apply lucas_primality 140084323 (2 : ZMod 140084323)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (1487, 1), (2243, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (1487, 1), (2243, 1)] : List FactorBlock).map factorBlockValue).prod) = 140084323 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_1487
      · exact prime_oneHundredFiftyTwoET_2243
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 140084323) ^ 70042161 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 140084323) ^ 46694774 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 140084323) ^ 20012046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 140084323) ^ 94206 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 140084323) ^ 62454 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_145393489 : Nat.Prime 145393489 := by
  apply lucas_primality 145393489 (7 : ZMod 145393489)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 3), (23, 1), (14633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 3), (23, 1), (14633, 1)] : List FactorBlock).map factorBlockValue).prod) = 145393489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_14633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 145393489) ^ 72696744 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 145393489) ^ 48464496 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 145393489) ^ 6321456 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 145393489) ^ 9936 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_163907389 : Nat.Prime 163907389 := by
  apply lucas_primality 163907389 (2 : ZMod 163907389)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 5), (168629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 5), (168629, 1)] : List FactorBlock).map factorBlockValue).prod) = 163907389 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_168629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 163907389) ^ 81953694 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 163907389) ^ 54635796 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 163907389) ^ 972 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_193897349 : Nat.Prime 193897349 := by
  apply lucas_primality 193897349 (2 : ZMod 193897349)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (797, 1), (60821, 1)] : List FactorBlock).map factorBlockValue).prod) = 193897349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_797
      · exact prime_oneHundredFiftyTwoET_60821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 193897349) ^ 96948674 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 243284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 193897349) ^ 3188 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_194084747 : Nat.Prime 194084747 := by
  apply lucas_primality 194084747 (2 : ZMod 194084747)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (109, 1), (251, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (109, 1), (251, 1), (3547, 1)] : List FactorBlock).map factorBlockValue).prod) = 194084747 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_109
      · exact prime_oneHundredFiftyTwoET_251
      · exact prime_oneHundredFiftyTwoET_3547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 194084747) ^ 97042373 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 1780594 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 773246 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 194084747) ^ 54718 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_225093833 : Nat.Prime 225093833 := by
  apply lucas_primality 225093833 (3 : ZMod 225093833)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (349, 1), (80621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (349, 1), (80621, 1)] : List FactorBlock).map factorBlockValue).prod) = 225093833 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_349
      · exact prime_oneHundredFiftyTwoET_80621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 225093833) ^ 112546916 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 225093833) ^ 644968 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 225093833) ^ 2792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_233755999 : Nat.Prime 233755999 := by
  apply lucas_primality 233755999 (7 : ZMod 233755999)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (43, 1), (71, 1), (1823, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (43, 1), (71, 1), (1823, 1)] : List FactorBlock).map factorBlockValue).prod) = 233755999 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_1823
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 233755999) ^ 116877999 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 233755999) ^ 77918666 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 233755999) ^ 33393714 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 233755999) ^ 5436186 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 233755999) ^ 3292338 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 233755999) ^ 128226 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_237269779 : Nat.Prime 237269779 := by
  apply lucas_primality 237269779 (2 : ZMod 237269779)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (39544963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (39544963, 1)] : List FactorBlock).map factorBlockValue).prod) = 237269779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_39544963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 237269779) ^ 118634889 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 237269779) ^ 79089926 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 237269779) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_247489127 : Nat.Prime 247489127 := by
  apply lucas_primality 247489127 (5 : ZMod 247489127)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (73, 1), (1695131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (73, 1), (1695131, 1)] : List FactorBlock).map factorBlockValue).prod) = 247489127 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_73
      · exact prime_oneHundredFiftyTwoET_1695131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 247489127) ^ 123744563 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 247489127) ^ 3390262 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 247489127) ^ 146 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_264206713 : Nat.Prime 264206713 := by
  apply lucas_primality 264206713 (5 : ZMod 264206713)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (11, 1), (142969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (11, 1), (142969, 1)] : List FactorBlock).map factorBlockValue).prod) = 264206713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_142969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 264206713) ^ 132103356 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 264206713) ^ 88068904 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 264206713) ^ 37743816 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 264206713) ^ 24018792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 264206713) ^ 1848 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_289317307 : Nat.Prime 289317307 := by
  apply lucas_primality 289317307 (2 : ZMod 289317307)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (48219551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (48219551, 1)] : List FactorBlock).map factorBlockValue).prod) = 289317307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_48219551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 289317307) ^ 144658653 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 289317307) ^ 96439102 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 289317307) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_424251137 : Nat.Prime 424251137 := by
  apply lucas_primality 424251137 (3 : ZMod 424251137)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (1657231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (1657231, 1)] : List FactorBlock).map factorBlockValue).prod) = 424251137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1657231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 424251137) ^ 212125568 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 424251137) ^ 256 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_426333337 : Nat.Prime 426333337 := by
  apply lucas_primality 426333337 (15 : ZMod 426333337)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 2), (13, 1), (23, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 2), (13, 1), (23, 1), (491, 1)] : List FactorBlock).map factorBlockValue).prod) = 426333337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (15 : ZMod 426333337) ^ 213166668 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 426333337) ^ 142111112 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 426333337) ^ 38757576 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 426333337) ^ 32794872 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 426333337) ^ 18536232 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (15 : ZMod 426333337) ^ 868296 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_453333809 : Nat.Prime 453333809 := by
  apply lucas_primality 453333809 (3 : ZMod 453333809)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (4481, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (4481, 1), (6323, 1)] : List FactorBlock).map factorBlockValue).prod) = 453333809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_4481
      · exact prime_oneHundredFiftyTwoET_6323
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 453333809) ^ 226666904 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 453333809) ^ 101168 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 453333809) ^ 71696 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_466649147 : Nat.Prime 466649147 := by
  apply lucas_primality 466649147 (2 : ZMod 466649147)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 1), (3824993, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 1), (3824993, 1)] : List FactorBlock).map factorBlockValue).prod) = 466649147 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_61
      · exact prime_oneHundredFiftyTwoET_3824993
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 466649147) ^ 233324573 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 466649147) ^ 7649986 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 466649147) ^ 122 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_497172713 : Nat.Prime 497172713 := by
  apply lucas_primality 497172713 (3 : ZMod 497172713)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (62146589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (62146589, 1)] : List FactorBlock).map factorBlockValue).prod) = 497172713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_62146589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 497172713) ^ 248586356 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 497172713) ^ 8 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_523166659 : Nat.Prime 523166659 := by
  apply lucas_primality 523166659 (2 : ZMod 523166659)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12456349, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12456349, 1)] : List FactorBlock).map factorBlockValue).prod) = 523166659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_12456349
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 523166659) ^ 261583329 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 523166659) ^ 174388886 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 523166659) ^ 74738094 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 523166659) ^ 42 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_572157373 : Nat.Prime 572157373 := by
  apply lucas_primality 572157373 (2 : ZMod 572157373)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (2804693, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (2804693, 1)] : List FactorBlock).map factorBlockValue).prod) = 572157373 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_2804693
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 572157373) ^ 286078686 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 572157373) ^ 190719124 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 572157373) ^ 33656316 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 572157373) ^ 204 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_583350533 : Nat.Prime 583350533 := by
  apply lucas_primality 583350533 (2 : ZMod 583350533)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1061, 1), (137453, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1061, 1), (137453, 1)] : List FactorBlock).map factorBlockValue).prod) = 583350533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1061
      · exact prime_oneHundredFiftyTwoET_137453
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 583350533) ^ 291675266 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 583350533) ^ 549812 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 583350533) ^ 4244 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_601205251 : Nat.Prime 601205251 := by
  apply lucas_primality 601205251 (2 : ZMod 601205251)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 3), (801607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 3), (801607, 1)] : List FactorBlock).map factorBlockValue).prod) = 601205251 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_801607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 601205251) ^ 300602625 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 601205251) ^ 200401750 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 601205251) ^ 120241050 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 601205251) ^ 750 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_615208637 : Nat.Prime 615208637 := by
  apply lucas_primality 615208637 (2 : ZMod 615208637)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (21971737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (21971737, 1)] : List FactorBlock).map factorBlockValue).prod) = 615208637 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_21971737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 615208637) ^ 307604318 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 615208637) ^ 87886948 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 615208637) ^ 28 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17203
      · exact prime_oneHundredFiftyTwoET_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_719187409 : Nat.Prime 719187409 := by
  apply lucas_primality 719187409 (11 : ZMod 719187409)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (4994357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (4994357, 1)] : List FactorBlock).map factorBlockValue).prod) = 719187409 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_4994357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 719187409) ^ 359593704 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 719187409) ^ 239729136 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 719187409) ^ 144 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_768177257 : Nat.Prime 768177257 := by
  apply lucas_primality 768177257 (3 : ZMod 768177257)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (11, 1), (409, 1), (3049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (11, 1), (409, 1), (3049, 1)] : List FactorBlock).map factorBlockValue).prod) = 768177257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_409
      · exact prime_oneHundredFiftyTwoET_3049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 768177257) ^ 384088628 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 768177257) ^ 109739608 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 768177257) ^ 69834296 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 768177257) ^ 1878184 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 768177257) ^ 251944 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_779529749 : Nat.Prime 779529749 := by
  apply lucas_primality 779529749 (2 : ZMod 779529749)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (809, 1), (240893, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (809, 1), (240893, 1)] : List FactorBlock).map factorBlockValue).prod) = 779529749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_809
      · exact prime_oneHundredFiftyTwoET_240893
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 779529749) ^ 389764874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 779529749) ^ 963572 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 779529749) ^ 3236 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_874671197 : Nat.Prime 874671197 := by
  apply lucas_primality 874671197 (2 : ZMod 874671197)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (31238257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (31238257, 1)] : List FactorBlock).map factorBlockValue).prod) = 874671197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_31238257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 874671197) ^ 437335598 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 874671197) ^ 124953028 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 874671197) ^ 28 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_888404761 : Nat.Prime 888404761 := by
  apply lucas_primality 888404761 (11 : ZMod 888404761)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (5, 1), (274199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (5, 1), (274199, 1)] : List FactorBlock).map factorBlockValue).prod) = 888404761 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_274199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 888404761) ^ 444202380 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 296134920 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 177680952 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 888404761) ^ 3240 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_896642093 : Nat.Prime 896642093 := by
  apply lucas_primality 896642093 (2 : ZMod 896642093)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (593, 1), (378011, 1)] : List FactorBlock).map factorBlockValue).prod) = 896642093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_593
      · exact prime_oneHundredFiftyTwoET_378011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 896642093) ^ 448321046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 1512044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 896642093) ^ 2372 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_914124779 : Nat.Prime 914124779 := by
  apply lucas_primality 914124779 (2 : ZMod 914124779)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1459, 1), (44753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1459, 1), (44753, 1)] : List FactorBlock).map factorBlockValue).prod) = 914124779 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_1459
      · exact prime_oneHundredFiftyTwoET_44753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 914124779) ^ 457062389 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 130589254 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 626542 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 914124779) ^ 20426 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_922142597 : Nat.Prime 922142597 := by
  apply lucas_primality 922142597 (2 : ZMod 922142597)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (14653, 1), (15733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (14653, 1), (15733, 1)] : List FactorBlock).map factorBlockValue).prod) = 922142597 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_14653
      · exact prime_oneHundredFiftyTwoET_15733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 922142597) ^ 461071298 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 922142597) ^ 62932 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 922142597) ^ 58612 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1005543181 : Nat.Prime 1005543181 := by
  apply lucas_primality 1005543181 (2 : ZMod 1005543181)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (5, 1), (71, 1), (26227, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (5, 1), (71, 1), (26227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1005543181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_26227
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1005543181) ^ 502771590 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005543181) ^ 335181060 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005543181) ^ 201108636 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005543181) ^ 14162580 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1005543181) ^ 38340 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1097098493 : Nat.Prime 1097098493 := by
  apply lucas_primality 1097098493 (2 : ZMod 1097098493)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (39182089, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (39182089, 1)] : List FactorBlock).map factorBlockValue).prod) = 1097098493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_39182089
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1097098493) ^ 548549246 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097098493) ^ 156728356 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1097098493) ^ 28 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1210850611 : Nat.Prime 1210850611 := by
  apply lucas_primality 1210850611 (2 : ZMod 1210850611)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (61, 2), (10847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (61, 2), (10847, 1)] : List FactorBlock).map factorBlockValue).prod) = 1210850611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_61
      · exact prime_oneHundredFiftyTwoET_10847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1210850611) ^ 605425305 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1210850611) ^ 403616870 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1210850611) ^ 242170122 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1210850611) ^ 19850010 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1210850611) ^ 111630 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1240049303 : Nat.Prime 1240049303 := by
  apply lucas_primality 1240049303 (5 : ZMod 1240049303)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (37, 1), (139, 1), (120557, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (37, 1), (139, 1), (120557, 1)] : List FactorBlock).map factorBlockValue).prod) = 1240049303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_37
      · exact prime_oneHundredFiftyTwoET_139
      · exact prime_oneHundredFiftyTwoET_120557
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1240049303) ^ 620024651 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1240049303) ^ 33514846 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1240049303) ^ 8921218 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1240049303) ^ 10286 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1280230753 : Nat.Prime 1280230753 := by
  apply lucas_primality 1280230753 (5 : ZMod 1280230753)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (29, 2), (101, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (29, 2), (101, 1), (157, 1)] : List FactorBlock).map factorBlockValue).prod) = 1280230753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_29
      · exact prime_oneHundredFiftyTwoET_101
      · exact prime_oneHundredFiftyTwoET_157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1280230753) ^ 640115376 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1280230753) ^ 426743584 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1280230753) ^ 44145888 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1280230753) ^ 12675552 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1280230753) ^ 8154336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1299989947 : Nat.Prime 1299989947 := by
  apply lucas_primality 1299989947 (2 : ZMod 1299989947)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1667, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 1299989947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_1667
      · exact prime_oneHundredFiftyTwoET_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1299989947) ^ 649994973 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 433329982 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 56521302 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 779838 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1299989947) ^ 230046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1593200489 : Nat.Prime 1593200489 := by
  apply lucas_primality 1593200489 (6 : ZMod 1593200489)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (2677, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (2677, 1), (6763, 1)] : List FactorBlock).map factorBlockValue).prod) = 1593200489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_2677
      · exact prime_oneHundredFiftyTwoET_6763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1593200489) ^ 796600244 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1593200489) ^ 144836408 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1593200489) ^ 595144 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1593200489) ^ 235576 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1645619411 : Nat.Prime 1645619411 := by
  apply lucas_primality 1645619411 (2 : ZMod 1645619411)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (23, 1), (313, 1), (22859, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (23, 1), (313, 1), (22859, 1)] : List FactorBlock).map factorBlockValue).prod) = 1645619411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_313
      · exact prime_oneHundredFiftyTwoET_22859
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1645619411) ^ 822809705 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645619411) ^ 329123882 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645619411) ^ 71548670 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645619411) ^ 5257570 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1645619411) ^ 71990 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1820857889 : Nat.Prime 1820857889 := by
  apply lucas_primality 1820857889 (3 : ZMod 1820857889)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (41, 1), (1387849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (41, 1), (1387849, 1)] : List FactorBlock).map factorBlockValue).prod) = 1820857889 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_41
      · exact prime_oneHundredFiftyTwoET_1387849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1820857889) ^ 910428944 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820857889) ^ 44411168 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1820857889) ^ 1312 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2372697791 : Nat.Prime 2372697791 := by
  apply lucas_primality 2372697791 (7 : ZMod 2372697791)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (237269779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (237269779, 1)] : List FactorBlock).map factorBlockValue).prod) = 2372697791 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_237269779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 2372697791) ^ 1186348895 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 2372697791) ^ 474539558 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 2372697791) ^ 10 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2416168199 : Nat.Prime 2416168199 := by
  apply lucas_primality 2416168199 (7 : ZMod 2416168199)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (71, 1), (362027, 1)] : List FactorBlock).map factorBlockValue).prod) = 2416168199 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_47
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_362027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 2416168199) ^ 1208084099 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 51407834 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 34030538 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 2416168199) ^ 6674 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2708662711 : Nat.Prime 2708662711 := by
  apply lucas_primality 2708662711 (6 : ZMod 2708662711)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 2), (534253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 2), (534253, 1)] : List FactorBlock).map factorBlockValue).prod) = 2708662711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_534253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2708662711) ^ 1354331355 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 902887570 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 541732542 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 208358670 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2708662711) ^ 5070 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3144650473 : Nat.Prime 3144650473 := by
  apply lucas_primality 3144650473 (7 : ZMod 3144650473)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (41, 1), (355087, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (41, 1), (355087, 1)] : List FactorBlock).map factorBlockValue).prod) = 3144650473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_41
      · exact prime_oneHundredFiftyTwoET_355087
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3144650473) ^ 1572325236 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3144650473) ^ 1048216824 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3144650473) ^ 76698792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3144650473) ^ 8856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3515265851 : Nat.Prime 3515265851 := by
  apply lucas_primality 3515265851 (2 : ZMod 3515265851)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (4783, 1), (14699, 1)] : List FactorBlock).map factorBlockValue).prod) = 3515265851 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_4783
      · exact prime_oneHundredFiftyTwoET_14699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3515265851) ^ 1757632925 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 703053170 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 734950 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3515265851) ^ 239150 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4287002677 : Nat.Prime 4287002677 := by
  apply lucas_primality 4287002677 (2 : ZMod 4287002677)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (1910429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (1910429, 1)] : List FactorBlock).map factorBlockValue).prod) = 4287002677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_1910429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4287002677) ^ 2143501338 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287002677) ^ 1429000892 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287002677) ^ 389727516 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287002677) ^ 252176628 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4287002677) ^ 2244 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4304480599 : Nat.Prime 4304480599 := by
  apply lucas_primality 4304480599 (11 : ZMod 4304480599)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (21739801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (21739801, 1)] : List FactorBlock).map factorBlockValue).prod) = 4304480599 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_21739801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 4304480599) ^ 2152240299 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 4304480599) ^ 1434826866 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 4304480599) ^ 391316418 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 4304480599) ^ 198 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4959861037 : Nat.Prime 4959861037 := by
  apply lucas_primality 4959861037 (2 : ZMod 4959861037)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (23, 1), (97, 1), (14251, 1)] : List FactorBlock).map factorBlockValue).prod) = 4959861037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_97
      · exact prime_oneHundredFiftyTwoET_14251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4959861037) ^ 2479930518 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 1653287012 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 381527772 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 215646132 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 51132588 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4959861037) ^ 348036 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_5324400491 : Nat.Prime 5324400491 := by
  apply lucas_primality 5324400491 (2 : ZMod 5324400491)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (6959, 1), (76511, 1)] : List FactorBlock).map factorBlockValue).prod) = 5324400491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_6959
      · exact prime_oneHundredFiftyTwoET_76511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5324400491) ^ 2662200245 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 1064880098 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 765110 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 5324400491) ^ 69590 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6012052511 : Nat.Prime 6012052511 := by
  apply lucas_primality 6012052511 (17 : ZMod 6012052511)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (601205251, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (601205251, 1)] : List FactorBlock).map factorBlockValue).prod) = 6012052511 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_601205251
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (17 : ZMod 6012052511) ^ 3006026255 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 6012052511) ^ 1202410502 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 6012052511) ^ 10 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_31
      · exact prime_oneHundredFiftyTwoET_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_7952358461 : Nat.Prime 7952358461 := by
  apply lucas_primality 7952358461 (2 : ZMod 7952358461)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1367, 1), (290869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1367, 1), (290869, 1)] : List FactorBlock).map factorBlockValue).prod) = 7952358461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_1367
      · exact prime_oneHundredFiftyTwoET_290869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7952358461) ^ 3976179230 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7952358461) ^ 1590471692 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7952358461) ^ 5817380 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7952358461) ^ 27340 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_8138000777 : Nat.Prime 8138000777 := by
  apply lucas_primality 8138000777 (3 : ZMod 8138000777)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (43, 1), (1391587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (43, 1), (1391587, 1)] : List FactorBlock).map factorBlockValue).prod) = 8138000777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_1391587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8138000777) ^ 4069000388 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 478705928 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 189255832 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8138000777) ^ 5848 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_13132498471 : Nat.Prime 13132498471 := by
  apply lucas_primality 13132498471 (3 : ZMod 13132498471)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (53, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (13, 1), (17, 1), (19, 1), (53, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 13132498471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_281
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13132498471) ^ 6566249235 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 4377499490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 2626499694 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 1876071210 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 1010192190 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 772499910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 691184130 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 247782990 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 13132498471) ^ 46734870 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_15991285699 : Nat.Prime 15991285699 := by
  apply lucas_primality 15991285699 (3 : ZMod 15991285699)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (888404761, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (888404761, 1)] : List FactorBlock).map factorBlockValue).prod) = 15991285699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_888404761
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 15991285699) ^ 7995642849 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 15991285699) ^ 5330428566 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 15991285699) ^ 18 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_19396018141 : Nat.Prime 19396018141 := by
  apply lucas_primality 19396018141 (2 : ZMod 19396018141)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (19, 1), (3923, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (19, 1), (3923, 1), (4337, 1)] : List FactorBlock).map factorBlockValue).prod) = 19396018141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_3923
      · exact prime_oneHundredFiftyTwoET_4337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19396018141) ^ 9698009070 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 19396018141) ^ 6465339380 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 19396018141) ^ 3879203628 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 19396018141) ^ 1020843060 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 19396018141) ^ 4944180 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 19396018141) ^ 4472220 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_19481132537 : Nat.Prime 19481132537 := by
  apply lucas_primality 19481132537 (3 : ZMod 19481132537)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (349, 1), (6977483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (349, 1), (6977483, 1)] : List FactorBlock).map factorBlockValue).prod) = 19481132537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_349
      · exact prime_oneHundredFiftyTwoET_6977483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 19481132537) ^ 9740566268 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 19481132537) ^ 55819864 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 19481132537) ^ 2792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_21972999679 : Nat.Prime 21972999679 := by
  apply lucas_primality 21972999679 (3 : ZMod 21972999679)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (523166659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (523166659, 1)] : List FactorBlock).map factorBlockValue).prod) = 21972999679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_523166659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 21972999679) ^ 10986499839 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 21972999679) ^ 7324333226 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 21972999679) ^ 3138999954 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 21972999679) ^ 42 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_22776090853 : Nat.Prime 22776090853 := by
  apply lucas_primality 22776090853 (2 : ZMod 22776090853)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (71, 1), (26732501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (71, 1), (26732501, 1)] : List FactorBlock).map factorBlockValue).prod) = 22776090853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_26732501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22776090853) ^ 11388045426 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 7592030284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 320790012 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 22776090853) ^ 852 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_24995319911 : Nat.Prime 24995319911 := by
  apply lucas_primality 24995319911 (7 : ZMod 24995319911)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (59, 1), (3851359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (59, 1), (3851359, 1)] : List FactorBlock).map factorBlockValue).prod) = 24995319911 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_3851359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 24995319911) ^ 12497659955 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 24995319911) ^ 4999063982 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 24995319911) ^ 2272301810 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 24995319911) ^ 423649490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 24995319911) ^ 6490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_34591821809 : Nat.Prime 34591821809 := by
  apply lucas_primality 34591821809 (3 : ZMod 34591821809)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (307, 1), (1019, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (307, 1), (1019, 1), (6911, 1)] : List FactorBlock).map factorBlockValue).prod) = 34591821809 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_307
      · exact prime_oneHundredFiftyTwoET_1019
      · exact prime_oneHundredFiftyTwoET_6911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34591821809) ^ 17295910904 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 34591821809) ^ 112676944 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 34591821809) ^ 33946832 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 34591821809) ^ 5005328 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_39933114467 : Nat.Prime 39933114467 := by
  apply lucas_primality 39933114467 (5 : ZMod 39933114467)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4801, 1), (594119, 1)] : List FactorBlock).map factorBlockValue).prod) = 39933114467 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_4801
      · exact prime_oneHundredFiftyTwoET_594119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 39933114467) ^ 19966557233 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 5704730638 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 8317666 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 39933114467) ^ 67214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_42938289203 : Nat.Prime 42938289203 := by
  apply lucas_primality 42938289203 (2 : ZMod 42938289203)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (19, 1), (1087, 1), (1039517, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (19, 1), (1087, 1), (1039517, 1)] : List FactorBlock).map factorBlockValue).prod) = 42938289203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_1087
      · exact prime_oneHundredFiftyTwoET_1039517
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 42938289203) ^ 21469144601 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 42938289203) ^ 2259909958 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 42938289203) ^ 39501646 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 42938289203) ^ 41306 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_53161332641 : Nat.Prime 53161332641 := by
  apply lucas_primality 53161332641 (3 : ZMod 53161332641)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (13, 1), (373, 1), (68521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (13, 1), (373, 1), (68521, 1)] : List FactorBlock).map factorBlockValue).prod) = 53161332641 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_373
      · exact prime_oneHundredFiftyTwoET_68521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 53161332641) ^ 26580666320 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 53161332641) ^ 10632266528 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 53161332641) ^ 4089333280 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 53161332641) ^ 142523680 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 53161332641) ^ 775840 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_55008928103 : Nat.Prime 55008928103 := by
  apply lucas_primality 55008928103 (5 : ZMod 55008928103)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (12553, 1), (2191067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (12553, 1), (2191067, 1)] : List FactorBlock).map factorBlockValue).prod) = 55008928103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_12553
      · exact prime_oneHundredFiftyTwoET_2191067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 55008928103) ^ 27504464051 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 55008928103) ^ 4382134 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 55008928103) ^ 25106 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_55813317187 : Nat.Prime 55813317187 := by
  apply lucas_primality 55813317187 (3 : ZMod 55813317187)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (16223, 1), (52127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (16223, 1), (52127, 1)] : List FactorBlock).map factorBlockValue).prod) = 55813317187 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_16223
      · exact prime_oneHundredFiftyTwoET_52127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 55813317187) ^ 27906658593 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813317187) ^ 18604439062 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813317187) ^ 5073937926 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813317187) ^ 3440382 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 55813317187) ^ 1070718 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_75499625869 : Nat.Prime 75499625869 := by
  apply lucas_primality 75499625869 (2 : ZMod 75499625869)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (4177, 1), (1506257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (4177, 1), (1506257, 1)] : List FactorBlock).map factorBlockValue).prod) = 75499625869 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_4177
      · exact prime_oneHundredFiftyTwoET_1506257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 75499625869) ^ 37749812934 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 75499625869) ^ 25166541956 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 75499625869) ^ 18075084 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 75499625869) ^ 50124 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_77195130737 : Nat.Prime 77195130737 := by
  apply lucas_primality 77195130737 (3 : ZMod 77195130737)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (827, 1), (253651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (827, 1), (253651, 1)] : List FactorBlock).map factorBlockValue).prod) = 77195130737 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_827
      · exact prime_oneHundredFiftyTwoET_253651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 77195130737) ^ 38597565368 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 77195130737) ^ 3356310032 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 77195130737) ^ 93343568 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 77195130737) ^ 304336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_88631475817 : Nat.Prime 88631475817 := by
  apply lucas_primality 88631475817 (5 : ZMod 88631475817)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (43, 1), (67, 1), (151, 1), (653, 1)] : List FactorBlock).map factorBlockValue).prod) = 88631475817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_151
      · exact prime_oneHundredFiftyTwoET_653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 88631475817) ^ 44315737908 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 29543825272 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 6817805832 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 2061197112 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 1322857848 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 586963416 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 88631475817) ^ 135729672 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_99779807873 : Nat.Prime 99779807873 := by
  apply lucas_primality 99779807873 (3 : ZMod 99779807873)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (779529749, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (779529749, 1)] : List FactorBlock).map factorBlockValue).prod) = 99779807873 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_779529749
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 99779807873) ^ 49889903936 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 99779807873) ^ 128 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_108333102277 : Nat.Prime 108333102277 := by
  apply lucas_primality 108333102277 (5 : ZMod 108333102277)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (17, 1), (103, 1), (245513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (17, 1), (103, 1), (245513, 1)] : List FactorBlock).map factorBlockValue).prod) = 108333102277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_103
      · exact prime_oneHundredFiftyTwoET_245513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 108333102277) ^ 54166551138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 108333102277) ^ 36111034092 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 108333102277) ^ 15476157468 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 108333102277) ^ 6372535428 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 108333102277) ^ 1051777692 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 108333102277) ^ 441252 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_112245555847 : Nat.Prime 112245555847 := by
  apply lucas_primality 112245555847 (3 : ZMod 112245555847)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (163, 1), (311, 1), (19423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (163, 1), (311, 1), (19423, 1)] : List FactorBlock).map factorBlockValue).prod) = 112245555847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_163
      · exact prime_oneHundredFiftyTwoET_311
      · exact prime_oneHundredFiftyTwoET_19423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 112245555847) ^ 56122777923 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 112245555847) ^ 37415185282 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 112245555847) ^ 5907660834 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 112245555847) ^ 688623042 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 112245555847) ^ 360918186 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 112245555847) ^ 5779002 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_116376108847 : Nat.Prime 116376108847 := by
  apply lucas_primality 116376108847 (3 : ZMod 116376108847)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19396018141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19396018141, 1)] : List FactorBlock).map factorBlockValue).prod) = 116376108847 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_19396018141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 116376108847) ^ 58188054423 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 116376108847) ^ 38792036282 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 116376108847) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_118356756277 : Nat.Prime 118356756277 := by
  apply lucas_primality 118356756277 (2 : ZMod 118356756277)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (896642093, 1)] : List FactorBlock).map factorBlockValue).prod) = 118356756277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_896642093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 118356756277) ^ 59178378138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 39452252092 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 10759705116 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 118356756277) ^ 132 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_143138630863 : Nat.Prime 143138630863 := by
  apply lucas_primality 143138630863 (6 : ZMod 143138630863)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (9949, 1), (799291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (9949, 1), (799291, 1)] : List FactorBlock).map factorBlockValue).prod) = 143138630863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_9949
      · exact prime_oneHundredFiftyTwoET_799291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 143138630863) ^ 71569315431 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 143138630863) ^ 47712876954 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 143138630863) ^ 14387238 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 143138630863) ^ 179082 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_144653921759 : Nat.Prime 144653921759 := by
  apply lucas_primality 144653921759 (7 : ZMod 144653921759)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3144650473, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3144650473, 1)] : List FactorBlock).map factorBlockValue).prod) = 144653921759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_3144650473
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 144653921759) ^ 72326960879 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 144653921759) ^ 6289300946 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 144653921759) ^ 46 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_197649551861 : Nat.Prime 197649551861 := by
  apply lucas_primality 197649551861 (2 : ZMod 197649551861)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (37, 1), (1931, 1), (138319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (37, 1), (1931, 1), (138319, 1)] : List FactorBlock).map factorBlockValue).prod) = 197649551861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_37
      · exact prime_oneHundredFiftyTwoET_1931
      · exact prime_oneHundredFiftyTwoET_138319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 197649551861) ^ 98824775930 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 197649551861) ^ 39529910372 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 197649551861) ^ 5341879780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 197649551861) ^ 102356060 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 197649551861) ^ 1428940 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_213553277447 : Nat.Prime 213553277447 := by
  apply lucas_primality 213553277447 (5 : ZMod 213553277447)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (139, 1), (768177257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (139, 1), (768177257, 1)] : List FactorBlock).map factorBlockValue).prod) = 213553277447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_139
      · exact prime_oneHundredFiftyTwoET_768177257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 213553277447) ^ 106776638723 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 213553277447) ^ 1536354514 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 213553277447) ^ 278 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_260947514731 : Nat.Prime 260947514731 := by
  apply lucas_primality 260947514731 (2 : ZMod 260947514731)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (379, 1), (79967, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (41, 1), (379, 1), (79967, 1)] : List FactorBlock).map factorBlockValue).prod) = 260947514731 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_41
      · exact prime_oneHundredFiftyTwoET_379
      · exact prime_oneHundredFiftyTwoET_79967
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 260947514731) ^ 130473757365 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 86982504910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 52189502946 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 37278216390 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 6364573530 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 688515870 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 260947514731) ^ 3263190 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_263840276839 : Nat.Prime 263840276839 := by
  apply lucas_primality 263840276839 (6 : ZMod 263840276839)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (97, 1), (453333809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (97, 1), (453333809, 1)] : List FactorBlock).map factorBlockValue).prod) = 263840276839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_97
      · exact prime_oneHundredFiftyTwoET_453333809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 263840276839) ^ 131920138419 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 263840276839) ^ 87946758946 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 263840276839) ^ 2720002854 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 263840276839) ^ 582 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_289307843519 : Nat.Prime 289307843519 := by
  apply lucas_primality 289307843519 (7 : ZMod 289307843519)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (144653921759, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (144653921759, 1)] : List FactorBlock).map factorBlockValue).prod) = 289307843519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_144653921759
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (7 : ZMod 289307843519) ^ 144653921759 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 289307843519) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_309922603129 : Nat.Prime 309922603129 := by
  apply lucas_primality 309922603129 (7 : ZMod 309922603129)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (4304480599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (4304480599, 1)] : List FactorBlock).map factorBlockValue).prod) = 309922603129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_4304480599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 309922603129) ^ 154961301564 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 309922603129) ^ 103307534376 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 309922603129) ^ 72 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_371414407073 : Nat.Prime 371414407073 := by
  apply lucas_primality 371414407073 (3 : ZMod 371414407073)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (71, 1), (463, 1), (18583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (71, 1), (463, 1), (18583, 1)] : List FactorBlock).map factorBlockValue).prod) = 371414407073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_463
      · exact prime_oneHundredFiftyTwoET_18583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 371414407073) ^ 185707203536 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 371414407073) ^ 19548126688 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 371414407073) ^ 5231188832 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 371414407073) ^ 802190944 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 371414407073) ^ 19986784 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_419501118209 : Nat.Prime 419501118209 := by
  apply lucas_primality 419501118209 (3 : ZMod 419501118209)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (109, 1), (2819, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (109, 1), (2819, 1), (5333, 1)] : List FactorBlock).map factorBlockValue).prod) = 419501118209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_109
      · exact prime_oneHundredFiftyTwoET_2819
      · exact prime_oneHundredFiftyTwoET_5333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 419501118209) ^ 209750559104 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 3848634112 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 148812032 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 419501118209) ^ 78661376 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_434222083417 : Nat.Prime 434222083417 := by
  apply lucas_primality 434222083417 (5 : ZMod 434222083417)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (11, 1), (19, 2), (4556179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (11, 1), (19, 2), (4556179, 1)] : List FactorBlock).map factorBlockValue).prod) = 434222083417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_4556179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 434222083417) ^ 217111041708 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 434222083417) ^ 144740694472 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 434222083417) ^ 39474734856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 434222083417) ^ 22853793864 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 434222083417) ^ 95304 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_472986682277 : Nat.Prime 472986682277 := by
  apply lucas_primality 472986682277 (2 : ZMod 472986682277)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (113, 1), (269, 1), (659, 1), (5903, 1)] : List FactorBlock).map factorBlockValue).prod) = 472986682277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_113
      · exact prime_oneHundredFiftyTwoET_269
      · exact prime_oneHundredFiftyTwoET_659
      · exact prime_oneHundredFiftyTwoET_5903
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 472986682277) ^ 236493341138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 4185722852 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 1758314804 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 717733964 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 472986682277) ^ 80126492 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_521791248119 : Nat.Prime 521791248119 := by
  apply lucas_primality 521791248119 (7 : ZMod 521791248119)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (5324400491, 1)] : List FactorBlock).map factorBlockValue).prod) = 521791248119 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_5324400491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 521791248119) ^ 260895624059 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 74541606874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 521791248119) ^ 98 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_553367035063 : Nat.Prime 553367035063 := by
  apply lucas_primality 553367035063 (3 : ZMod 553367035063)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (53, 1), (7951, 1), (72953, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (53, 1), (7951, 1), (72953, 1)] : List FactorBlock).map factorBlockValue).prod) = 553367035063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_7951
      · exact prime_oneHundredFiftyTwoET_72953
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 553367035063) ^ 276683517531 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 553367035063) ^ 184455678354 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 553367035063) ^ 10440887454 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 553367035063) ^ 69597162 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 553367035063) ^ 7585254 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_621220372301 : Nat.Prime 621220372301 := by
  apply lucas_primality 621220372301 (2 : ZMod 621220372301)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (11, 1), (53, 1), (10655581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (11, 1), (53, 1), (10655581, 1)] : List FactorBlock).map factorBlockValue).prod) = 621220372301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_10655581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 621220372301) ^ 310610186150 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 621220372301) ^ 124244074460 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 621220372301) ^ 56474579300 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 621220372301) ^ 11721139100 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 621220372301) ^ 58300 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_636480833207 : Nat.Prime 636480833207 := by
  apply lucas_primality 636480833207 (5 : ZMod 636480833207)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (22807, 1), (324503, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (22807, 1), (324503, 1)] : List FactorBlock).map factorBlockValue).prod) = 636480833207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_22807
      · exact prime_oneHundredFiftyTwoET_324503
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 636480833207) ^ 318240416603 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 636480833207) ^ 14801879842 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 636480833207) ^ 27907258 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 636480833207) ^ 1961402 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_812260148269 : Nat.Prime 812260148269 := by
  apply lucas_primality 812260148269 (2 : ZMod 812260148269)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (257, 1), (3347, 1), (78691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (257, 1), (3347, 1), (78691, 1)] : List FactorBlock).map factorBlockValue).prod) = 812260148269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_257
      · exact prime_oneHundredFiftyTwoET_3347
      · exact prime_oneHundredFiftyTwoET_78691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 812260148269) ^ 406130074134 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 270753382756 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 3160545324 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 242683044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 812260148269) ^ 10322148 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_970782332161 : Nat.Prime 970782332161 := by
  apply lucas_primality 970782332161 (13 : ZMod 970782332161)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 1), (97, 1), (2606267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 1), (97, 1), (2606267, 1)] : List FactorBlock).map factorBlockValue).prod) = 970782332161 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_97
      · exact prime_oneHundredFiftyTwoET_2606267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 970782332161) ^ 485391166080 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 970782332161) ^ 323594110720 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 970782332161) ^ 194156466432 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 970782332161) ^ 10008065280 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 970782332161) ^ 372480 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1102635976397 : Nat.Prime 1102635976397 := by
  apply lucas_primality 1102635976397 (2 : ZMod 1102635976397)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (163, 1), (99479969, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (163, 1), (99479969, 1)] : List FactorBlock).map factorBlockValue).prod) = 1102635976397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_163
      · exact prime_oneHundredFiftyTwoET_99479969
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1102635976397) ^ 551317988198 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102635976397) ^ 64860939788 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102635976397) ^ 6764637892 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1102635976397) ^ 11084 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1288148676091 : Nat.Prime 1288148676091 := by
  apply lucas_primality 1288148676091 (2 : ZMod 1288148676091)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (42938289203, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (42938289203, 1)] : List FactorBlock).map factorBlockValue).prod) = 1288148676091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_42938289203
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1288148676091) ^ 644074338045 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1288148676091) ^ 429382892030 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1288148676091) ^ 257629735218 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1288148676091) ^ 30 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1734429894853 : Nat.Prime 1734429894853 := by
  apply lucas_primality 1734429894853 (5 : ZMod 1734429894853)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (67, 1), (431, 1), (5005223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (67, 1), (431, 1), (5005223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1734429894853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_431
      · exact prime_oneHundredFiftyTwoET_5005223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 1734429894853) ^ 867214947426 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734429894853) ^ 578143298284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734429894853) ^ 25887013356 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734429894853) ^ 4024199292 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1734429894853) ^ 346524 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1840088312581 : Nat.Prime 1840088312581 := by
  apply lucas_primality 1840088312581 (6 : ZMod 1840088312581)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (8167, 1), (536447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (8167, 1), (536447, 1)] : List FactorBlock).map factorBlockValue).prod) = 1840088312581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_8167
      · exact prime_oneHundredFiftyTwoET_536447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 1840088312581) ^ 920044156290 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840088312581) ^ 613362770860 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840088312581) ^ 368017662516 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840088312581) ^ 262869758940 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840088312581) ^ 225307740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 1840088312581) ^ 3430140 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2020049643697 : Nat.Prime 2020049643697 := by
  apply lucas_primality 2020049643697 (10 : ZMod 2020049643697)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (6012052511, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (6012052511, 1)] : List FactorBlock).map factorBlockValue).prod) = 2020049643697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_6012052511
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 2020049643697) ^ 1010024821848 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 2020049643697) ^ 673349881232 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 2020049643697) ^ 288578520528 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (10 : ZMod 2020049643697) ^ 336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2725028037883 : Nat.Prime 2725028037883 := by
  apply lucas_primality 2725028037883 (3 : ZMod 2725028037883)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (191, 1), (264206713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (191, 1), (264206713, 1)] : List FactorBlock).map factorBlockValue).prod) = 2725028037883 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_191
      · exact prime_oneHundredFiftyTwoET_264206713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2725028037883) ^ 1362514018941 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2725028037883) ^ 908342679294 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2725028037883) ^ 14267162502 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2725028037883) ^ 10314 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3939562007093 : Nat.Prime 3939562007093 := by
  apply lucas_primality 3939562007093 (2 : ZMod 3939562007093)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (85733, 1), (244423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (85733, 1), (244423, 1)] : List FactorBlock).map factorBlockValue).prod) = 3939562007093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_47
      · exact prime_oneHundredFiftyTwoET_85733
      · exact prime_oneHundredFiftyTwoET_244423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3939562007093) ^ 1969781003546 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3939562007093) ^ 83820468236 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3939562007093) ^ 45951524 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3939562007093) ^ 16117804 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4289837606129 : Nat.Prime 4289837606129 := by
  apply lucas_primality 4289837606129 (3 : ZMod 4289837606129)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (113, 1), (2372697791, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (113, 1), (2372697791, 1)] : List FactorBlock).map factorBlockValue).prod) = 4289837606129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_113
      · exact prime_oneHundredFiftyTwoET_2372697791
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 4289837606129) ^ 2144918803064 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 4289837606129) ^ 37963164656 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 4289837606129) ^ 1808 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_5277649833569 : Nat.Prime 5277649833569 := by
  apply lucas_primality 5277649833569 (3 : ZMod 5277649833569)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (19, 1), (1240049303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (19, 1), (1240049303, 1)] : List FactorBlock).map factorBlockValue).prod) = 5277649833569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_1240049303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 5277649833569) ^ 2638824916784 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 5277649833569) ^ 753949976224 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 5277649833569) ^ 277771043872 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 5277649833569) ^ 4256 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6967771917713 : Nat.Prime 6967771917713 := by
  apply lucas_primality 6967771917713 (3 : ZMod 6967771917713)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (17, 1), (79, 1), (167, 1), (439, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (17, 1), (79, 1), (167, 1), (439, 1), (4423, 1)] : List FactorBlock).map factorBlockValue).prod) = 6967771917713 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_79
      · exact prime_oneHundredFiftyTwoET_167
      · exact prime_oneHundredFiftyTwoET_439
      · exact prime_oneHundredFiftyTwoET_4423
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6967771917713) ^ 3483885958856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6967771917713) ^ 409868936336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6967771917713) ^ 88199644528 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6967771917713) ^ 41723185136 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6967771917713) ^ 15871917808 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6967771917713) ^ 1575349744 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_8445825078233 : Nat.Prime 8445825078233 := by
  apply lucas_primality 8445825078233 (3 : ZMod 8445825078233)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (17, 1), (71, 1), (874671197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (17, 1), (71, 1), (874671197, 1)] : List FactorBlock).map factorBlockValue).prod) = 8445825078233 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_874671197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 8445825078233) ^ 4222912539116 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8445825078233) ^ 496813239896 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8445825078233) ^ 118955282792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 8445825078233) ^ 9656 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_9228659865181 : Nat.Prime 9228659865181 := by
  apply lucas_primality 9228659865181 (2 : ZMod 9228659865181)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (21972999679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (21972999679, 1)] : List FactorBlock).map factorBlockValue).prod) = 9228659865181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_21972999679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9228659865181) ^ 4614329932590 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 9228659865181) ^ 3076219955060 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 9228659865181) ^ 1845731973036 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 9228659865181) ^ 1318379980740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 9228659865181) ^ 420 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_9785892628279 : Nat.Prime 9785892628279 := by
  apply lucas_primality 9785892628279 (6 : ZMod 9785892628279)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (13, 1), (229, 1), (20291147, 1)] : List FactorBlock).map factorBlockValue).prod) = 9785892628279 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_229
      · exact prime_oneHundredFiftyTwoET_20291147
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 9785892628279) ^ 4892946314139 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 3261964209426 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 752760971406 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 42733155582 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 9785892628279) ^ 482274 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_10217866768471 : Nat.Prime 10217866768471 := by
  apply lucas_primality 10217866768471 (3 : ZMod 10217866768471)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (1489, 1), (89597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (23, 1), (37, 1), (1489, 1), (89597, 1)] : List FactorBlock).map factorBlockValue).prod) = 10217866768471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_37
      · exact prime_oneHundredFiftyTwoET_1489
      · exact prime_oneHundredFiftyTwoET_89597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10217866768471) ^ 5108933384235 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 3405955589490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 2043573353694 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 444255076890 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 276158561310 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 6862234230 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10217866768471) ^ 114042510 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_10403988322733 : Nat.Prime 10403988322733 := by
  apply lucas_primality 10403988322733 (2 : ZMod 10403988322733)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1303, 1), (2383, 1), (837667, 1)] : List FactorBlock).map factorBlockValue).prod) = 10403988322733 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1303
      · exact prime_oneHundredFiftyTwoET_2383
      · exact prime_oneHundredFiftyTwoET_837667
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10403988322733) ^ 5201994161366 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 7984641844 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 4365920404 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10403988322733) ^ 12420196 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_11821650773203 : Nat.Prime 11821650773203 := by
  apply lucas_primality 11821650773203 (2 : ZMod 11821650773203)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (19, 1), (1280230753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (19, 1), (1280230753, 1)] : List FactorBlock).map factorBlockValue).prod) = 11821650773203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_1280230753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 11821650773203) ^ 5910825386601 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 11821650773203) ^ 3940550257734 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 11821650773203) ^ 622192145958 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 11821650773203) ^ 9234 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_14334243066613 : Nat.Prime 14334243066613 := by
  apply lucas_primality 14334243066613 (2 : ZMod 14334243066613)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (7, 2), (2708662711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (7, 2), (2708662711, 1)] : List FactorBlock).map factorBlockValue).prod) = 14334243066613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_2708662711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14334243066613) ^ 7167121533306 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 4778081022204 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 2047749009516 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14334243066613) ^ 5292 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_14495928166849 : Nat.Prime 14495928166849 := by
  apply lucas_primality 14495928166849 (7 : ZMod 14495928166849)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (75499625869, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (75499625869, 1)] : List FactorBlock).map factorBlockValue).prod) = 14495928166849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_75499625869
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 14495928166849) ^ 7247964083424 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 14495928166849) ^ 4831976055616 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 14495928166849) ^ 192 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_26255962099621 : Nat.Prime 26255962099621 := by
  apply lucas_primality 26255962099621 (6 : ZMod 26255962099621)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (11, 1), (38351, 1), (345769, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (11, 1), (38351, 1), (345769, 1)] : List FactorBlock).map factorBlockValue).prod) = 26255962099621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_38351
      · exact prime_oneHundredFiftyTwoET_345769
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 26255962099621) ^ 13127981049810 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 8751987366540 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 5251192419924 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 2386905645420 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 684622620 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 26255962099621) ^ 75934980 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_28567378430231 : Nat.Prime 28567378430231 := by
  apply lucas_primality 28567378430231 (7 : ZMod 28567378430231)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (223, 1), (8779, 1), (76801, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (223, 1), (8779, 1), (76801, 1)] : List FactorBlock).map factorBlockValue).prod) = 28567378430231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_223
      · exact prime_oneHundredFiftyTwoET_8779
      · exact prime_oneHundredFiftyTwoET_76801
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 28567378430231) ^ 14283689215115 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 28567378430231) ^ 5713475686046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 28567378430231) ^ 1503546233170 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 28567378430231) ^ 128104836010 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 28567378430231) ^ 3254058370 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 28567378430231) ^ 371966230 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_30382232469499 : Nat.Prime 30382232469499 := by
  apply lucas_primality 30382232469499 (3 : ZMod 30382232469499)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 2), (13, 1), (34283, 1), (77291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 2), (13, 1), (34283, 1), (77291, 1)] : List FactorBlock).map factorBlockValue).prod) = 30382232469499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_34283
      · exact prime_oneHundredFiftyTwoET_77291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 30382232469499) ^ 15191116234749 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 30382232469499) ^ 10127410823166 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 30382232469499) ^ 4340318924214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 30382232469499) ^ 2337094805346 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 30382232469499) ^ 886218606 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 30382232469499) ^ 393088878 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_33181458080039 : Nat.Prime 33181458080039 := by
  apply lucas_primality 33181458080039 (11 : ZMod 33181458080039)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (285317, 1), (58148407, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (285317, 1), (58148407, 1)] : List FactorBlock).map factorBlockValue).prod) = 33181458080039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_285317
      · exact prime_oneHundredFiftyTwoET_58148407
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 33181458080039) ^ 16590729040019 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 33181458080039) ^ 116296814 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 33181458080039) ^ 570634 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_35481804872093 : Nat.Prime 35481804872093 := by
  apply lucas_primality 35481804872093 (3 : ZMod 35481804872093)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (521791248119, 1)] : List FactorBlock).map factorBlockValue).prod) = 35481804872093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_521791248119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 35481804872093) ^ 17740902436046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 2087164992476 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 35481804872093) ^ 68 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_37404377760941 : Nat.Prime 37404377760941 := by
  apply lucas_primality 37404377760941 (2 : ZMod 37404377760941)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (379177, 1), (4932311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (379177, 1), (4932311, 1)] : List FactorBlock).map factorBlockValue).prod) = 37404377760941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_379177
      · exact prime_oneHundredFiftyTwoET_4932311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37404377760941) ^ 18702188880470 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404377760941) ^ 7480875552188 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404377760941) ^ 98646220 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37404377760941) ^ 7583540 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_37714774023317 : Nat.Prime 37714774023317 := by
  apply lucas_primality 37714774023317 (2 : ZMod 37714774023317)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (49741, 1), (14581213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (49741, 1), (14581213, 1)] : List FactorBlock).map factorBlockValue).prod) = 37714774023317 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_49741
      · exact prime_oneHundredFiftyTwoET_14581213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 37714774023317) ^ 18857387011658 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37714774023317) ^ 2901136463332 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37714774023317) ^ 758223076 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 37714774023317) ^ 2586532 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_40481942876783 : Nat.Prime 40481942876783 := by
  apply lucas_primality 40481942876783 (5 : ZMod 40481942876783)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (1840088312581, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (1840088312581, 1)] : List FactorBlock).map factorBlockValue).prod) = 40481942876783 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_1840088312581
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 40481942876783) ^ 20240971438391 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 40481942876783) ^ 3680176625162 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 40481942876783) ^ 22 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_49250493410207 : Nat.Prime 49250493410207 := by
  apply lucas_primality 49250493410207 (5 : ZMod 49250493410207)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (29, 1), (77195130737, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (29, 1), (77195130737, 1)] : List FactorBlock).map factorBlockValue).prod) = 49250493410207 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_29
      · exact prime_oneHundredFiftyTwoET_77195130737
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 49250493410207) ^ 24625246705103 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 49250493410207) ^ 4477317582746 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 49250493410207) ^ 1698292876214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 49250493410207) ^ 638 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_57861568703801 : Nat.Prime 57861568703801 := by
  apply lucas_primality 57861568703801 (3 : ZMod 57861568703801)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (289307843519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (289307843519, 1)] : List FactorBlock).map factorBlockValue).prod) = 57861568703801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_289307843519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 57861568703801) ^ 28930784351900 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 57861568703801) ^ 11572313740760 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 57861568703801) ^ 200 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_61654569369979 : Nat.Prime 61654569369979 := by
  apply lucas_primality 61654569369979 (2 : ZMod 61654569369979)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (19, 1), (2243, 1), (18547603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (19, 1), (2243, 1), (18547603, 1)] : List FactorBlock).map factorBlockValue).prod) = 61654569369979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_2243
      · exact prime_oneHundredFiftyTwoET_18547603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 61654569369979) ^ 30827284684989 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61654569369979) ^ 20551523123326 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61654569369979) ^ 4742659182306 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61654569369979) ^ 3244977335262 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61654569369979) ^ 27487547646 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 61654569369979) ^ 3324126 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_70753820440643 : Nat.Prime 70753820440643 := by
  apply lucas_primality 70753820440643 (2 : ZMod 70753820440643)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (431, 1), (54833, 1), (1496927, 1)] : List FactorBlock).map factorBlockValue).prod) = 70753820440643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_431
      · exact prime_oneHundredFiftyTwoET_54833
      · exact prime_oneHundredFiftyTwoET_1496927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 70753820440643) ^ 35376910220321 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 164161996382 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 1290351074 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 70753820440643) ^ 47266046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_80313035030381 : Nat.Prime 80313035030381 := by
  apply lucas_primality 80313035030381 (2 : ZMod 80313035030381)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (73, 1), (55008928103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (73, 1), (55008928103, 1)] : List FactorBlock).map factorBlockValue).prod) = 80313035030381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_73
      · exact prime_oneHundredFiftyTwoET_55008928103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 80313035030381) ^ 40156517515190 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 80313035030381) ^ 16062607006076 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 80313035030381) ^ 1100178562060 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 80313035030381) ^ 1460 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_80963885753567 : Nat.Prime 80963885753567 := by
  apply lucas_primality 80963885753567 (5 : ZMod 80963885753567)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (40481942876783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (40481942876783, 1)] : List FactorBlock).map factorBlockValue).prod) = 80963885753567 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_40481942876783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 80963885753567) ^ 40481942876783 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 80963885753567) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_83611192864571 : Nat.Prime 83611192864571 := by
  apply lucas_primality 83611192864571 (2 : ZMod 83611192864571)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (47, 1), (53, 1), (67, 1), (7156783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (47, 1), (53, 1), (67, 1), (7156783, 1)] : List FactorBlock).map factorBlockValue).prod) = 83611192864571 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_47
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_7156783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 83611192864571) ^ 41805596432285 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 16722238572914 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 11944456123510 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 1778961550310 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 1577569676690 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 1247928251710 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 83611192864571) ^ 11682790 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_94652655590939 : Nat.Prime 94652655590939 := by
  apply lucas_primality 94652655590939 (2 : ZMod 94652655590939)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3695257, 1), (12807317, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3695257, 1), (12807317, 1)] : List FactorBlock).map factorBlockValue).prod) = 94652655590939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3695257
      · exact prime_oneHundredFiftyTwoET_12807317
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 94652655590939) ^ 47326327795469 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 94652655590939) ^ 25614634 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 94652655590939) ^ 7390514 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_102220692905371 : Nat.Prime 102220692905371 := by
  apply lucas_primality 102220692905371 (2 : ZMod 102220692905371)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (101, 1), (1571, 1), (97169, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (17, 1), (101, 1), (1571, 1), (97169, 1)] : List FactorBlock).map factorBlockValue).prod) = 102220692905371 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_101
      · exact prime_oneHundredFiftyTwoET_1571
      · exact prime_oneHundredFiftyTwoET_97169
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 102220692905371) ^ 51110346452685 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 34073564301790 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 20444138581074 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 7863130223490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 6012981935610 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 1012086068370 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 65067277470 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 102220692905371) ^ 1051988730 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_107173596754699 : Nat.Prime 107173596754699 := by
  apply lucas_primality 107173596754699 (2 : ZMod 107173596754699)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1117, 1), (15991285699, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1117, 1), (15991285699, 1)] : List FactorBlock).map factorBlockValue).prod) = 107173596754699 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_1117
      · exact prime_oneHundredFiftyTwoET_15991285699
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 107173596754699) ^ 53586798377349 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 35724532251566 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 95947714194 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 107173596754699) ^ 6702 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_120170927531489 : Nat.Prime 120170927531489 := by
  apply lucas_primality 120170927531489 (3 : ZMod 120170927531489)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (197649551861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (197649551861, 1)] : List FactorBlock).map factorBlockValue).prod) = 120170927531489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_197649551861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 120170927531489) ^ 60085463765744 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 120170927531489) ^ 6324785659552 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 120170927531489) ^ 608 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_126428729024569 : Nat.Prime 126428729024569 := by
  apply lucas_primality 126428729024569 (7 : ZMod 126428729024569)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (7069, 1), (39221387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (7069, 1), (39221387, 1)] : List FactorBlock).map factorBlockValue).prod) = 126428729024569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_7069
      · exact prime_oneHundredFiftyTwoET_39221387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 126428729024569) ^ 63214364512284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 126428729024569) ^ 42142909674856 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 126428729024569) ^ 6654143632872 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 126428729024569) ^ 17884952472 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 126428729024569) ^ 3223464 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_131733782284399 : Nat.Prime 131733782284399 := by
  apply lucas_primality 131733782284399 (6 : ZMod 131733782284399)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (59, 1), (53161332641, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (59, 1), (53161332641, 1)] : List FactorBlock).map factorBlockValue).prod) = 131733782284399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_53161332641
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 131733782284399) ^ 65866891142199 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 131733782284399) ^ 43911260761466 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 131733782284399) ^ 18819111754914 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 131733782284399) ^ 2232775970922 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 131733782284399) ^ 2478 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_160626070060763 : Nat.Prime 160626070060763 := by
  apply lucas_primality 160626070060763 (2 : ZMod 160626070060763)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (80313035030381, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (80313035030381, 1)] : List FactorBlock).map factorBlockValue).prod) = 160626070060763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_80313035030381
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 160626070060763) ^ 80313035030381 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 160626070060763) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_170734257263771 : Nat.Prime 170734257263771 := by
  apply lucas_primality 170734257263771 (2 : ZMod 170734257263771)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (379681, 1), (44967817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (379681, 1), (44967817, 1)] : List FactorBlock).map factorBlockValue).prod) = 170734257263771 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_379681
      · exact prime_oneHundredFiftyTwoET_44967817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 170734257263771) ^ 85367128631885 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 170734257263771) ^ 34146851452754 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 170734257263771) ^ 449678170 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 170734257263771) ^ 3796810 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_173340728312093 : Nat.Prime 173340728312093 := by
  apply lucas_primality 173340728312093 (2 : ZMod 173340728312093)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (3939562007093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (3939562007093, 1)] : List FactorBlock).map factorBlockValue).prod) = 173340728312093 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_3939562007093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 173340728312093) ^ 86670364156046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 173340728312093) ^ 15758248028372 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 173340728312093) ^ 44 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_258862483991359 : Nat.Prime 258862483991359 := by
  apply lucas_primality 258862483991359 (6 : ZMod 258862483991359)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (13, 1), (10789, 1), (102534983, 1)] : List FactorBlock).map factorBlockValue).prod) = 258862483991359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_10789
      · exact prime_oneHundredFiftyTwoET_102534983
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 258862483991359) ^ 129431241995679 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 86287494663786 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 19912498768566 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 23993186022 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 258862483991359) ^ 2524626 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_347902276004377 : Nat.Prime 347902276004377 := by
  apply lucas_primality 347902276004377 (5 : ZMod 347902276004377)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (14495928166849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (14495928166849, 1)] : List FactorBlock).map factorBlockValue).prod) = 347902276004377 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_14495928166849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 347902276004377) ^ 173951138002188 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 347902276004377) ^ 115967425334792 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 347902276004377) ^ 24 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_385664107977107 : Nat.Prime 385664107977107 := by
  apply lucas_primality 385664107977107 (2 : ZMod 385664107977107)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (113, 1), (5647, 1), (43170289, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (113, 1), (5647, 1), (43170289, 1)] : List FactorBlock).map factorBlockValue).prod) = 385664107977107 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_113
      · exact prime_oneHundredFiftyTwoET_5647
      · exact prime_oneHundredFiftyTwoET_43170289
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 385664107977107) ^ 192832053988553 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 385664107977107) ^ 55094872568158 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 385664107977107) ^ 3412956707762 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 385664107977107) ^ 68295397198 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 385664107977107) ^ 8933554 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_419816165275813 : Nat.Prime 419816165275813 := by
  apply lucas_primality 419816165275813 (2 : ZMod 419816165275813)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (17, 1), (211427, 1), (9733489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (17, 1), (211427, 1), (9733489, 1)] : List FactorBlock).map factorBlockValue).prod) = 419816165275813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_211427
      · exact prime_oneHundredFiftyTwoET_9733489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 419816165275813) ^ 209908082637906 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 419816165275813) ^ 139938721758604 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 419816165275813) ^ 24695068545636 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 419816165275813) ^ 1985631756 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 419816165275813) ^ 43131108 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_435418472849621 : Nat.Prime 435418472849621 := by
  apply lucas_primality 435418472849621 (2 : ZMod 435418472849621)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (67, 1), (24995319911, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (67, 1), (24995319911, 1)] : List FactorBlock).map factorBlockValue).prod) = 435418472849621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_24995319911
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 435418472849621) ^ 217709236424810 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 435418472849621) ^ 87083694569924 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 435418472849621) ^ 33493728680740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 435418472849621) ^ 6498783176860 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 435418472849621) ^ 17420 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_485783314521403 : Nat.Prime 485783314521403 := by
  apply lucas_primality 485783314521403 (3 : ZMod 485783314521403)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (80963885753567, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (80963885753567, 1)] : List FactorBlock).map factorBlockValue).prod) = 485783314521403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_80963885753567
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 485783314521403) ^ 242891657260701 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 485783314521403) ^ 161927771507134 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 485783314521403) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_598339625465863 : Nat.Prime 598339625465863 := by
  apply lucas_primality 598339625465863 (5 : ZMod 598339625465863)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (43, 2), (271, 1), (3159001, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (43, 2), (271, 1), (3159001, 1)] : List FactorBlock).map factorBlockValue).prod) = 598339625465863 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_271
      · exact prime_oneHundredFiftyTwoET_3159001
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 598339625465863) ^ 299169812732931 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 598339625465863) ^ 199446541821954 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 598339625465863) ^ 85477089352266 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 598339625465863) ^ 13914875010834 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 598339625465863) ^ 2207895296922 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 598339625465863) ^ 189407862 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_625249011082109 : Nat.Prime 625249011082109 := by
  apply lucas_primality 625249011082109 (2 : ZMod 625249011082109)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (19, 1), (71, 1), (181, 1), (91454369, 1)] : List FactorBlock).map factorBlockValue).prod) = 625249011082109 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_181
      · exact prime_oneHundredFiftyTwoET_91454369
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 625249011082109) ^ 312624505541054 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 89321287297444 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 32907842688532 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 8806324099748 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 3454414425868 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 625249011082109) ^ 6836732 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_726340956728039 : Nat.Prime 726340956728039 := by
  apply lucas_primality 726340956728039 (7 : ZMod 726340956728039)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43, 1), (8445825078233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43, 1), (8445825078233, 1)] : List FactorBlock).map factorBlockValue).prod) = 726340956728039 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_8445825078233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 726340956728039) ^ 363170478364019 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 726340956728039) ^ 16891650156466 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 726340956728039) ^ 86 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_870684648627301 : Nat.Prime 870684648627301 := by
  apply lucas_primality 870684648627301 (2 : ZMod 870684648627301)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (13, 1), (17, 1), (13132498471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (13, 1), (17, 1), (13132498471, 1)] : List FactorBlock).map factorBlockValue).prod) = 870684648627301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_13132498471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 870684648627301) ^ 435342324313650 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 290228216209100 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 174136929725460 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 66975742202100 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 51216744036900 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 870684648627301) ^ 66300 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1115331887063311 : Nat.Prime 1115331887063311 := by
  apply lucas_primality 1115331887063311 (7 : ZMod 1115331887063311)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 2), (19, 1), (39933114467, 1)] : List FactorBlock).map factorBlockValue).prod) = 1115331887063311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_39933114467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 1115331887063311) ^ 557665943531655 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 371777295687770 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 223066377412662 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 159333126723330 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 58701678266490 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 1115331887063311) ^ 27930 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1291737826932829 : Nat.Prime 1291737826932829 := by
  apply lucas_primality 1291737826932829 (2 : ZMod 1291737826932829)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (9785892628279, 1)] : List FactorBlock).map factorBlockValue).prod) = 1291737826932829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_9785892628279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1291737826932829) ^ 645868913466414 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 430579275644276 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 117430711539348 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1291737826932829) ^ 132 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1365874058110169 : Nat.Prime 1365874058110169 := by
  apply lucas_primality 1365874058110169 (3 : ZMod 1365874058110169)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (170734257263771, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (170734257263771, 1)] : List FactorBlock).map factorBlockValue).prod) = 1365874058110169 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_170734257263771
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1365874058110169) ^ 682937029055084 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1365874058110169) ^ 8 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1482930802749359 : Nat.Prime 1482930802749359 := by
  apply lucas_primality 1482930802749359 (13 : ZMod 1482930802749359)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (61, 2), (71, 1), (541, 1), (1951, 1), (2659, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (61, 2), (71, 1), (541, 1), (1951, 1), (2659, 1)] : List FactorBlock).map factorBlockValue).prod) = 1482930802749359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_61
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_541
      · exact prime_oneHundredFiftyTwoET_1951
      · exact prime_oneHundredFiftyTwoET_2659
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 1482930802749359) ^ 741465401374679 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 1482930802749359) ^ 24310341028678 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 1482930802749359) ^ 20886349334498 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 1482930802749359) ^ 2741092056838 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 1482930802749359) ^ 760087546258 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 1482930802749359) ^ 557702445562 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1906052673410411 : Nat.Prime 1906052673410411 := by
  apply lucas_primality 1906052673410411 (2 : ZMod 1906052673410411)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (17, 1), (23, 1), (214807, 1), (324199, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (17, 1), (23, 1), (214807, 1), (324199, 1)] : List FactorBlock).map factorBlockValue).prod) = 1906052673410411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_214807
      · exact prime_oneHundredFiftyTwoET_324199
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1906052673410411) ^ 953026336705205 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 381210534682082 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 272293239058630 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 112120745494730 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 82871855365670 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 8873326630 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1906052673410411) ^ 5879267590 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2139920090441051 : Nat.Prime 2139920090441051 := by
  apply lucas_primality 2139920090441051 (2 : ZMod 2139920090441051)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (83, 1), (347, 1), (653, 1), (2275657, 1)] : List FactorBlock).map factorBlockValue).prod) = 2139920090441051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_83
      · exact prime_oneHundredFiftyTwoET_347
      · exact prime_oneHundredFiftyTwoET_653
      · exact prime_oneHundredFiftyTwoET_2275657
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2139920090441051) ^ 1069960045220525 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 427984018088210 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 25782169764350 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 6166916687150 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 3277059862850 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2139920090441051) ^ 940352650 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2577361185181577 : Nat.Prime 2577361185181577 := by
  apply lucas_primality 2577361185181577 (3 : ZMod 2577361185181577)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (6134851, 1), (52514747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (6134851, 1), (52514747, 1)] : List FactorBlock).map factorBlockValue).prod) = 2577361185181577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_6134851
      · exact prime_oneHundredFiftyTwoET_52514747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2577361185181577) ^ 1288680592590788 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2577361185181577) ^ 420117976 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2577361185181577) ^ 49078808 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3400146116944931 : Nat.Prime 3400146116944931 := by
  apply lucas_primality 3400146116944931 (7 : ZMod 3400146116944931)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1303, 1), (260947514731, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1303, 1), (260947514731, 1)] : List FactorBlock).map factorBlockValue).prod) = 3400146116944931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_1303
      · exact prime_oneHundredFiftyTwoET_260947514731
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 3400146116944931) ^ 1700073058472465 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3400146116944931) ^ 680029223388986 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3400146116944931) ^ 2609475147310 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 3400146116944931) ^ 13030 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_5415812829868801 : Nat.Prime 5415812829868801 := by
  apply lucas_primality 5415812829868801 (7 : ZMod 5415812829868801)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (5, 2), (17, 1), (29, 1), (572157373, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (5, 2), (17, 1), (29, 1), (572157373, 1)] : List FactorBlock).map factorBlockValue).prod) = 5415812829868801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_29
      · exact prime_oneHundredFiftyTwoET_572157373
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 5415812829868801) ^ 2707906414934400 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 5415812829868801) ^ 1805270943289600 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 5415812829868801) ^ 1083162565973760 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 5415812829868801) ^ 318577225286400 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 5415812829868801) ^ 186752166547200 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 5415812829868801) ^ 9465600 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6145560041686553 : Nat.Prime 6145560041686553 := by
  apply lucas_primality 6145560041686553 (3 : ZMod 6145560041686553)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (151, 1), (197, 2), (5699467, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (151, 1), (197, 2), (5699467, 1)] : List FactorBlock).map factorBlockValue).prod) = 6145560041686553 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_151
      · exact prime_oneHundredFiftyTwoET_197
      · exact prime_oneHundredFiftyTwoET_5699467
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 6145560041686553) ^ 3072780020843276 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 267198262682024 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 40699073123752 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 31195736252216 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 6145560041686553) ^ 1078269256 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6374511739318903 : Nat.Prime 6374511739318903 := by
  apply lucas_primality 6374511739318903 (5 : ZMod 6374511739318903)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (30713, 1), (34591821809, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (30713, 1), (34591821809, 1)] : List FactorBlock).map factorBlockValue).prod) = 6374511739318903 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_30713
      · exact prime_oneHundredFiftyTwoET_34591821809
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 6374511739318903) ^ 3187255869659451 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6374511739318903) ^ 2124837246439634 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6374511739318903) ^ 207550930854 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6374511739318903) ^ 184278 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_7600654503810013 : Nat.Prime 7600654503810013 := by
  apply lucas_primality 7600654503810013 (2 : ZMod 7600654503810013)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (19, 2), (46327, 1), (37872883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (19, 2), (46327, 1), (37872883, 1)] : List FactorBlock).map factorBlockValue).prod) = 7600654503810013 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_46327
      · exact prime_oneHundredFiftyTwoET_37872883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 7600654503810013) ^ 3800327251905006 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7600654503810013) ^ 2533551501270004 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7600654503810013) ^ 400034447568948 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7600654503810013) ^ 164065329156 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 7600654503810013) ^ 200688564 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_8708369456992421 : Nat.Prime 8708369456992421 := by
  apply lucas_primality 8708369456992421 (2 : ZMod 8708369456992421)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (435418472849621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (435418472849621, 1)] : List FactorBlock).map factorBlockValue).prod) = 8708369456992421 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_435418472849621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8708369456992421) ^ 4354184728496210 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 8708369456992421) ^ 1741673891398484 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 8708369456992421) ^ 20 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_10463952414478393 : Nat.Prime 10463952414478393 := by
  apply lucas_primality 10463952414478393 (5 : ZMod 10463952414478393)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (17, 1), (11887, 1), (719187409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (17, 1), (11887, 1), (719187409, 1)] : List FactorBlock).map factorBlockValue).prod) = 10463952414478393 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_11887
      · exact prime_oneHundredFiftyTwoET_719187409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 10463952414478393) ^ 5231976207239196 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 10463952414478393) ^ 3487984138159464 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 10463952414478393) ^ 615526612616376 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 10463952414478393) ^ 880285388616 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 10463952414478393) ^ 14549688 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_12109621601860291 : Nat.Prime 12109621601860291 := by
  apply lucas_primality 12109621601860291 (3 : ZMod 12109621601860291)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (54437, 1), (145393489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (54437, 1), (145393489, 1)] : List FactorBlock).map factorBlockValue).prod) = 12109621601860291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_54437
      · exact prime_oneHundredFiftyTwoET_145393489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12109621601860291) ^ 6054810800930145 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 12109621601860291) ^ 4036540533953430 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 12109621601860291) ^ 2421924320372058 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 12109621601860291) ^ 712330682462370 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 12109621601860291) ^ 222452038170 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 12109621601860291) ^ 83288610 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_14765453512034683 : Nat.Prime 14765453512034683 := by
  apply lucas_primality 14765453512034683 (2 : ZMod 14765453512034683)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (2692093, 1), (914124779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (2692093, 1), (914124779, 1)] : List FactorBlock).map factorBlockValue).prod) = 14765453512034683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_2692093
      · exact prime_oneHundredFiftyTwoET_914124779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14765453512034683) ^ 7382726756017341 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 4921817837344894 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 5484748674 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14765453512034683) ^ 16152558 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_17668867706683931 : Nat.Prime 17668867706683931 := by
  apply lucas_primality 17668867706683931 (2 : ZMod 17668867706683931)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 1), (160626070060763, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 1), (160626070060763, 1)] : List FactorBlock).map factorBlockValue).prod) = 17668867706683931 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_160626070060763
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17668867706683931) ^ 8834433853341965 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 17668867706683931) ^ 3533773541336786 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 17668867706683931) ^ 1606260700607630 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 17668867706683931) ^ 110 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_20007968354627489 : Nat.Prime 20007968354627489 := by
  apply lucas_primality 20007968354627489 (3 : ZMod 20007968354627489)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (625249011082109, 1)] : List FactorBlock).map factorBlockValue).prod) = 20007968354627489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_625249011082109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 20007968354627489) ^ 10003984177313744 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 20007968354627489) ^ 32 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_20071895499760837 : Nat.Prime 20071895499760837 := by
  apply lucas_primality 20071895499760837 (2 : ZMod 20071895499760837)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1723, 1), (970782332161, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1723, 1), (970782332161, 1)] : List FactorBlock).map factorBlockValue).prod) = 20071895499760837 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_1723
      · exact prime_oneHundredFiftyTwoET_970782332161
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 20071895499760837) ^ 10035947749880418 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071895499760837) ^ 6690631833253612 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071895499760837) ^ 11649387985932 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 20071895499760837) ^ 20676 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_21494683197158071 : Nat.Prime 21494683197158071 := by
  apply lucas_primality 21494683197158071 (6 : ZMod 21494683197158071)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (3221, 1), (57737, 1), (3852697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (3221, 1), (57737, 1), (3852697, 1)] : List FactorBlock).map factorBlockValue).prod) = 21494683197158071 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_3221
      · exact prime_oneHundredFiftyTwoET_57737
      · exact prime_oneHundredFiftyTwoET_3852697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 21494683197158071) ^ 10747341598579035 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 21494683197158071) ^ 7164894399052690 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 21494683197158071) ^ 4298936639431614 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 21494683197158071) ^ 6673295000670 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 21494683197158071) ^ 372286111110 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 21494683197158071) ^ 5579126310 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_37051420944511243 : Nat.Prime 37051420944511243 := by
  apply lucas_primality 37051420944511243 (3 : ZMod 37051420944511243)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (131, 1), (170603, 1), (92103133, 1)] : List FactorBlock).map factorBlockValue).prod) = 37051420944511243 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_131
      · exact prime_oneHundredFiftyTwoET_170603
      · exact prime_oneHundredFiftyTwoET_92103133
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 37051420944511243) ^ 18525710472255621 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 12350473648170414 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 282835274385582 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 217179187614 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 37051420944511243) ^ 402281874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_47254495754060453 : Nat.Prime 47254495754060453 := by
  apply lucas_primality 47254495754060453 (2 : ZMod 47254495754060453)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (13, 1), (425653, 1), (194084747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (13, 1), (425653, 1), (194084747, 1)] : List FactorBlock).map factorBlockValue).prod) = 47254495754060453 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_425653
      · exact prime_oneHundredFiftyTwoET_194084747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 47254495754060453) ^ 23627247877030226 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 4295863250369132 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 3634961211850804 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 111016475284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 47254495754060453) ^ 243473516 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_51678990468932339 : Nat.Prime 51678990468932339 := by
  apply lucas_primality 51678990468932339 (2 : ZMod 51678990468932339)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (385664107977107, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (385664107977107, 1)] : List FactorBlock).map factorBlockValue).prod) = 51678990468932339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_385664107977107
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 51678990468932339) ^ 25839495234466169 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51678990468932339) ^ 771328215954214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51678990468932339) ^ 134 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_54102410473047011 : Nat.Prime 54102410473047011 := by
  apply lucas_primality 54102410473047011 (2 : ZMod 54102410473047011)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (5867033, 1), (922142597, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (5867033, 1), (922142597, 1)] : List FactorBlock).map factorBlockValue).prod) = 54102410473047011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_5867033
      · exact prime_oneHundredFiftyTwoET_922142597
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 54102410473047011) ^ 27051205236523505 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 54102410473047011) ^ 10820482094609402 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 54102410473047011) ^ 9221425970 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 54102410473047011) ^ 58670330 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_70075919093336591 : Nat.Prime 70075919093336591 := by
  apply lucas_primality 70075919093336591 (14 : ZMod 70075919093336591)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (24841, 1), (1299989947, 1)] : List FactorBlock).map factorBlockValue).prod) = 70075919093336591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_31
      · exact prime_oneHundredFiftyTwoET_24841
      · exact prime_oneHundredFiftyTwoET_1299989947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 70075919093336591) ^ 35037959546668295 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 14015183818667318 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 10010845584762370 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2260513519139890 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 2820978184990 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 70075919093336591) ^ 53904970 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_78988689197821061 : Nat.Prime 78988689197821061 := by
  apply lucas_primality 78988689197821061 (3 : ZMod 78988689197821061)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (29, 1), (145219, 1), (133972429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (29, 1), (145219, 1), (133972429, 1)] : List FactorBlock).map factorBlockValue).prod) = 78988689197821061 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_29
      · exact prime_oneHundredFiftyTwoET_145219
      · exact prime_oneHundredFiftyTwoET_133972429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 78988689197821061) ^ 39494344598910530 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 78988689197821061) ^ 15797737839564212 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 78988689197821061) ^ 11284098456831580 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 78988689197821061) ^ 2723747903373140 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 78988689197821061) ^ 543928061740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 78988689197821061) ^ 589589140 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_81130593224918807 : Nat.Prime 81130593224918807 := by
  apply lucas_primality 81130593224918807 (5 : ZMod 81130593224918807)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (163907389, 1), (247489127, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (163907389, 1), (247489127, 1)] : List FactorBlock).map factorBlockValue).prod) = 81130593224918807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_163907389
      · exact prime_oneHundredFiftyTwoET_247489127
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 81130593224918807) ^ 40565296612459403 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 81130593224918807) ^ 494978254 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 81130593224918807) ^ 327814778 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_86715016733573927 : Nat.Prime 86715016733573927 := by
  apply lucas_primality 86715016733573927 (5 : ZMod 86715016733573927)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (7001, 1), (213553277447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (7001, 1), (213553277447, 1)] : List FactorBlock).map factorBlockValue).prod) = 86715016733573927 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_29
      · exact prime_oneHundredFiftyTwoET_7001
      · exact prime_oneHundredFiftyTwoET_213553277447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 86715016733573927) ^ 43357508366786963 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 86715016733573927) ^ 2990172990812894 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 86715016733573927) ^ 12386090091926 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 86715016733573927) ^ 406058 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_88960470325245151 : Nat.Prime 88960470325245151 := by
  apply lucas_primality 88960470325245151 (3 : ZMod 88960470325245151)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (325709, 1), (1820857889, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (325709, 1), (1820857889, 1)] : List FactorBlock).map factorBlockValue).prod) = 88960470325245151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_325709
      · exact prime_oneHundredFiftyTwoET_1820857889
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 88960470325245151) ^ 44480235162622575 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88960470325245151) ^ 29653490108415050 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88960470325245151) ^ 17792094065049030 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88960470325245151) ^ 273128683350 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88960470325245151) ^ 48856350 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_157977378395642123 : Nat.Prime 157977378395642123 := by
  apply lucas_primality 157977378395642123 (2 : ZMod 157977378395642123)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (78988689197821061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (78988689197821061, 1)] : List FactorBlock).map factorBlockValue).prod) = 157977378395642123 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_78988689197821061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 157977378395642123) ^ 78988689197821061 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 157977378395642123) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_172424237385860321 : Nat.Prime 172424237385860321 := by
  apply lucas_primality 172424237385860321 (3 : ZMod 172424237385860321)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (7, 1), (463, 1), (3623, 1), (91776389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (7, 1), (463, 1), (3623, 1), (91776389, 1)] : List FactorBlock).map factorBlockValue).prod) = 172424237385860321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_463
      · exact prime_oneHundredFiftyTwoET_3623
      · exact prime_oneHundredFiftyTwoET_91776389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 172424237385860321) ^ 86212118692930160 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 172424237385860321) ^ 34484847477172064 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 172424237385860321) ^ 24632033912265760 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 172424237385860321) ^ 372406560228640 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 172424237385860321) ^ 47591564279840 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 172424237385860321) ^ 1878742880 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_324747509332878703 : Nat.Prime 324747509332878703 := by
  apply lucas_primality 324747509332878703 (3 : ZMod 324747509332878703)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2577361185181577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2577361185181577, 1)] : List FactorBlock).map factorBlockValue).prod) = 324747509332878703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_2577361185181577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 324747509332878703) ^ 162373754666439351 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 324747509332878703) ^ 108249169777626234 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 324747509332878703) ^ 46392501333268386 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 324747509332878703) ^ 126 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_344848474771720643 : Nat.Prime 344848474771720643 := by
  apply lucas_primality 344848474771720643 (2 : ZMod 344848474771720643)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (172424237385860321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (172424237385860321, 1)] : List FactorBlock).map factorBlockValue).prod) = 344848474771720643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_172424237385860321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 344848474771720643) ^ 172424237385860321 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 344848474771720643) ^ 2 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_841983229614766891 : Nat.Prime 841983229614766891 := by
  apply lucas_primality 841983229614766891 (3 : ZMod 841983229614766891)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (113, 1), (35481804872093, 1)] : List FactorBlock).map factorBlockValue).prod) = 841983229614766891 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_113
      · exact prime_oneHundredFiftyTwoET_35481804872093
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 841983229614766891) ^ 420991614807383445 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 280661076538255630 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 168396645922953378 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 120283318516395270 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 7451179023139530 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 841983229614766891) ^ 23730 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_947864270373852739 : Nat.Prime 947864270373852739 := by
  apply lucas_primality 947864270373852739 (2 : ZMod 947864270373852739)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (157977378395642123, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (157977378395642123, 1)] : List FactorBlock).map factorBlockValue).prod) = 947864270373852739 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_157977378395642123
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 947864270373852739) ^ 473932135186926369 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 947864270373852739) ^ 315954756791284246 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 947864270373852739) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_985685610646165501 : Nat.Prime 985685610646165501 := by
  apply lucas_primality 985685610646165501 (6 : ZMod 985685610646165501)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (5, 3), (1273421, 1), (19112231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (5, 3), (1273421, 1), (19112231, 1)] : List FactorBlock).map factorBlockValue).prod) = 985685610646165501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_1273421
      · exact prime_oneHundredFiftyTwoET_19112231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 985685610646165501) ^ 492842805323082750 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 985685610646165501) ^ 328561870215388500 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 985685610646165501) ^ 197137122129233100 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 985685610646165501) ^ 774045355500 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 985685610646165501) ^ 51573550500 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1094482698133098257 : Nat.Prime 1094482698133098257 := by
  apply lucas_primality 1094482698133098257 (3 : ZMod 1094482698133098257)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (491, 1), (1493, 1), (259201, 1), (360007, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (491, 1), (1493, 1), (259201, 1), (360007, 1)] : List FactorBlock).map factorBlockValue).prod) = 1094482698133098257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_491
      · exact prime_oneHundredFiftyTwoET_1493
      · exact prime_oneHundredFiftyTwoET_259201
      · exact prime_oneHundredFiftyTwoET_360007
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1094482698133098257) ^ 547241349066549128 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1094482698133098257) ^ 2229088998234416 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1094482698133098257) ^ 733076154141392 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1094482698133098257) ^ 4222524983056 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1094482698133098257) ^ 3040170602608 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1740874811875804673 : Nat.Prime 1740874811875804673 := by
  apply lucas_primality 1740874811875804673 (3 : ZMod 1740874811875804673)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 9), (3400146116944931, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 9), (3400146116944931, 1)] : List FactorBlock).map factorBlockValue).prod) = 1740874811875804673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3400146116944931
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 1740874811875804673) ^ 870437405937902336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 1740874811875804673) ^ 512 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1755553804145763163 : Nat.Prime 1755553804145763163 := by
  apply lucas_primality 1755553804145763163 (11 : ZMod 1755553804145763163)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (29297, 1), (434222083417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (29297, 1), (434222083417, 1)] : List FactorBlock).map factorBlockValue).prod) = 1755553804145763163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_29297
      · exact prime_oneHundredFiftyTwoET_434222083417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 1755553804145763163) ^ 877776902072881581 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 1755553804145763163) ^ 585184601381921054 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 1755553804145763163) ^ 76328426267207094 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 1755553804145763163) ^ 59922647511546 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (11 : ZMod 1755553804145763163) ^ 4042986 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1867585842648450817 : Nat.Prime 1867585842648450817 := by
  apply lucas_primality 1867585842648450817 (5 : ZMod 1867585842648450817)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 8), (3, 1), (349, 1), (6967771917713, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 8), (3, 1), (349, 1), (6967771917713, 1)] : List FactorBlock).map factorBlockValue).prod) = 1867585842648450817 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_349
      · exact prime_oneHundredFiftyTwoET_6967771917713
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1867585842648450817) ^ 933792921324225408 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1867585842648450817) ^ 622528614216150272 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1867585842648450817) ^ 5351248832803584 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 1867585842648450817) ^ 268032 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_101
      · exact prime_oneHundredFiftyTwoET_191
      · exact prime_oneHundredFiftyTwoET_48017
      · exact prime_oneHundredFiftyTwoET_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2624576590222488607 : Nat.Prime 2624576590222488607 := by
  apply lucas_primality 2624576590222488607 (3 : ZMod 2624576590222488607)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (97, 1), (137, 1), (919, 1), (15451, 1), (62653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (97, 1), (137, 1), (919, 1), (15451, 1), (62653, 1)] : List FactorBlock).map factorBlockValue).prod) = 2624576590222488607 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_37
      · exact prime_oneHundredFiftyTwoET_97
      · exact prime_oneHundredFiftyTwoET_137
      · exact prime_oneHundredFiftyTwoET_919
      · exact prime_oneHundredFiftyTwoET_15451
      · exact prime_oneHundredFiftyTwoET_62653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2624576590222488607) ^ 1312288295111244303 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 874858863407496202 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 70934502438445638 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 27057490620850398 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 19157493359288238 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 2855904885987474 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 169864512990906 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 2624576590222488607) ^ 41890677066102 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3131215697962690573 : Nat.Prime 3131215697962690573 := by
  apply lucas_primality 3131215697962690573 (2 : ZMod 3131215697962690573)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (20071895499760837, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (20071895499760837, 1)] : List FactorBlock).map factorBlockValue).prod) = 3131215697962690573 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_20071895499760837
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 3131215697962690573) ^ 1565607848981345286 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3131215697962690573) ^ 1043738565987563524 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3131215697962690573) ^ 240862745997130044 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3131215697962690573) ^ 156 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3503795954666829551 : Nat.Prime 3503795954666829551 := by
  apply lucas_primality 3503795954666829551 (13 : ZMod 3503795954666829551)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (70075919093336591, 1)] : List FactorBlock).map factorBlockValue).prod) = 3503795954666829551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_70075919093336591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (13 : ZMod 3503795954666829551) ^ 1751897977333414775 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 700759190933365910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 3503795954666829551) ^ 50 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4068832858225057777 : Nat.Prime 4068832858225057777 := by
  apply lucas_primality 4068832858225057777 (5 : ZMod 4068832858225057777)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (7, 1), (12109621601860291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (7, 1), (12109621601860291, 1)] : List FactorBlock).map factorBlockValue).prod) = 4068832858225057777 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_12109621601860291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 4068832858225057777) ^ 2034416429112528888 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 4068832858225057777) ^ 1356277619408352592 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 4068832858225057777) ^ 581261836889293968 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 4068832858225057777) ^ 336 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6868617687843709687 : Nat.Prime 6868617687843709687 := by
  apply lucas_primality 6868617687843709687 (5 : ZMod 6868617687843709687)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (23, 1), (59, 1), (99529, 1), (1210850611, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (23, 1), (59, 1), (99529, 1), (1210850611, 1)] : List FactorBlock).map factorBlockValue).prod) = 6868617687843709687 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_99529
      · exact prime_oneHundredFiftyTwoET_1210850611
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6868617687843709687) ^ 3434308843921854843 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 2289539229281236562 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 981231098263387098 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 298635551645378682 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 116417248946503554 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 69011219723334 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 6868617687843709687) ^ 5672555826 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_7828028820389715601 : Nat.Prime 7828028820389715601 := by
  apply lucas_primality 7828028820389715601 (7 : ZMod 7828028820389715601)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 2), (13, 1), (53, 1), (79, 1), (97, 1), (199, 1), (6208691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 2), (13, 1), (53, 1), (79, 1), (97, 1), (199, 1), (6208691, 1)] : List FactorBlock).map factorBlockValue).prod) = 7828028820389715601 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_79
      · exact prime_oneHundredFiftyTwoET_97
      · exact prime_oneHundredFiftyTwoET_199
      · exact prime_oneHundredFiftyTwoET_6208691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7828028820389715601) ^ 3914014410194857800 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 2609342940129905200 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 1565605764077943120 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 602156063106901200 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 147698656988485200 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 99088972409996400 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 80701328045254800 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 39336828243164400 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7828028820389715601) ^ 1260817911600 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_10998980608285723099 : Nat.Prime 10998980608285723099 := by
  apply lucas_primality 10998980608285723099 (2 : ZMod 10998980608285723099)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (427327, 1), (4289837606129, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (427327, 1), (4289837606129, 1)] : List FactorBlock).map factorBlockValue).prod) = 10998980608285723099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_427327
      · exact prime_oneHundredFiftyTwoET_4289837606129
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 10998980608285723099) ^ 5499490304142861549 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10998980608285723099) ^ 3666326869428574366 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10998980608285723099) ^ 25739025636774 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 10998980608285723099) ^ 2563962 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_13606243083093724621 : Nat.Prime 13606243083093724621 := by
  apply lucas_primality 13606243083093724621 (2 : ZMod 13606243083093724621)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (379, 1), (598339625465863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (379, 1), (598339625465863, 1)] : List FactorBlock).map factorBlockValue).prod) = 13606243083093724621 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_379
      · exact prime_oneHundredFiftyTwoET_598339625465863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13606243083093724621) ^ 6803121541546862310 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 13606243083093724621) ^ 4535414361031241540 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 13606243083093724621) ^ 2721248616618744924 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 13606243083093724621) ^ 35900377527951780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 13606243083093724621) ^ 22740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_34594553351042402261 : Nat.Prime 34594553351042402261 := by
  apply lucas_primality 34594553351042402261 (2 : ZMod 34594553351042402261)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (43, 1), (193, 1), (229, 1), (299099, 1), (3042997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (43, 1), (193, 1), (229, 1), (299099, 1), (3042997, 1)] : List FactorBlock).map factorBlockValue).prod) = 34594553351042402261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_193
      · exact prime_oneHundredFiftyTwoET_229
      · exact prime_oneHundredFiftyTwoET_299099
      · exact prime_oneHundredFiftyTwoET_3042997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 34594553351042402261) ^ 17297276675521201130 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 6918910670208480452 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 804524496535869820 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 179246390419908820 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 151067918563503940 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 115662551031740 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 34594553351042402261) ^ 11368579512580 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_36633597620505094679 : Nat.Prime 36633597620505094679 := by
  apply lucas_primality 36633597620505094679 (7 : ZMod 36633597620505094679)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (3121, 1), (764209, 1), (1097098493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (3121, 1), (764209, 1), (1097098493, 1)] : List FactorBlock).map factorBlockValue).prod) = 36633597620505094679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_3121
      · exact prime_oneHundredFiftyTwoET_764209
      · exact prime_oneHundredFiftyTwoET_1097098493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 36633597620505094679) ^ 18316798810252547339 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 36633597620505094679) ^ 5233371088643584954 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 36633597620505094679) ^ 11737775591318518 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 36633597620505094679) ^ 47936621553142 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 36633597620505094679) ^ 33391348046 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_38295590219153007821 : Nat.Prime 38295590219153007821 := by
  apply lucas_primality 38295590219153007821 (2 : ZMod 38295590219153007821)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1801, 1), (3511, 1), (510199, 1), (593519, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1801, 1), (3511, 1), (510199, 1), (593519, 1)] : List FactorBlock).map factorBlockValue).prod) = 38295590219153007821 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_1801
      · exact prime_oneHundredFiftyTwoET_3511
      · exact prime_oneHundredFiftyTwoET_510199
      · exact prime_oneHundredFiftyTwoET_593519
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 38295590219153007821) ^ 19147795109576503910 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 7659118043830601564 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 21263514835731820 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 10907317066121620 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 75060104428180 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 38295590219153007821) ^ 64522938977780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_41573873765184175469 : Nat.Prime 41573873765184175469 := by
  apply lucas_primality 41573873765184175469 (2 : ZMod 41573873765184175469)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (223, 1), (233, 1), (888661, 1), (225093833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (223, 1), (233, 1), (888661, 1), (225093833, 1)] : List FactorBlock).map factorBlockValue).prod) = 41573873765184175469 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_223
      · exact prime_oneHundredFiftyTwoET_233
      · exact prime_oneHundredFiftyTwoET_888661
      · exact prime_oneHundredFiftyTwoET_225093833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 41573873765184175469) ^ 20786936882592087734 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 41573873765184175469) ^ 186429927198135316 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 41573873765184175469) ^ 178428642769030796 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 41573873765184175469) ^ 46782601875388 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 41573873765184175469) ^ 184695747596 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_56191330843355904697 : Nat.Prime 56191330843355904697 := by
  apply lucas_primality 56191330843355904697 (5 : ZMod 56191330843355904697)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 4), (86715016733573927, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 4), (86715016733573927, 1)] : List FactorBlock).map factorBlockValue).prod) = 56191330843355904697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_86715016733573927
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 56191330843355904697) ^ 28095665421677952348 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 56191330843355904697) ^ 18730443614451968232 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 56191330843355904697) ^ 648 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_81637458498562347727 : Nat.Prime 81637458498562347727 := by
  apply lucas_primality 81637458498562347727 (3 : ZMod 81637458498562347727)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13606243083093724621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13606243083093724621, 1)] : List FactorBlock).map factorBlockValue).prod) = 81637458498562347727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13606243083093724621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 81637458498562347727) ^ 40818729249281173863 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 81637458498562347727) ^ 27212486166187449242 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 81637458498562347727) ^ 6 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_88711704958154895091 : Nat.Prime 88711704958154895091 := by
  apply lucas_primality 88711704958154895091 (3 : ZMod 88711704958154895091)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (985685610646165501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (985685610646165501, 1)] : List FactorBlock).map factorBlockValue).prod) = 88711704958154895091 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_985685610646165501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 88711704958154895091) ^ 44355852479077447545 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88711704958154895091) ^ 29570568319384965030 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88711704958154895091) ^ 17742340991630979018 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 88711704958154895091) ^ 90 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_97190505030529514209 : Nat.Prime 97190505030529514209 := by
  apply lucas_primality 97190505030529514209 (13 : ZMod 97190505030529514209)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (5051, 1), (11437, 1), (1593200489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (5051, 1), (11437, 1), (1593200489, 1)] : List FactorBlock).map factorBlockValue).prod) = 97190505030529514209 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_5051
      · exact prime_oneHundredFiftyTwoET_11437
      · exact prime_oneHundredFiftyTwoET_1593200489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 97190505030529514209) ^ 48595252515264757104 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 97190505030529514209) ^ 32396835010176504736 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 97190505030529514209) ^ 8835500457320864928 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 97190505030529514209) ^ 19241834296283808 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 97190505030529514209) ^ 8497901987455584 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (13 : ZMod 97190505030529514209) ^ 61003311072 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_241779130672718629297 : Nat.Prime 241779130672718629297 := by
  apply lucas_primality 241779130672718629297 (5 : ZMod 241779130672718629297)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (883, 1), (7207, 1), (263840276839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (883, 1), (7207, 1), (263840276839, 1)] : List FactorBlock).map factorBlockValue).prod) = 241779130672718629297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_883
      · exact prime_oneHundredFiftyTwoET_7207
      · exact prime_oneHundredFiftyTwoET_263840276839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 241779130672718629297) ^ 120889565336359314648 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 241779130672718629297) ^ 80593043557572876432 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 241779130672718629297) ^ 273815550025728912 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 241779130672718629297) ^ 33547818880632528 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 241779130672718629297) ^ 916384464 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_703934758930286278337 : Nat.Prime 703934758930286278337 := by
  apply lucas_primality 703934758930286278337 (3 : ZMod 703934758930286278337)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (10998980608285723099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (10998980608285723099, 1)] : List FactorBlock).map factorBlockValue).prod) = 703934758930286278337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_10998980608285723099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 703934758930286278337) ^ 351967379465143139168 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 703934758930286278337) ^ 64 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1533073286664614735179 : Nat.Prime 1533073286664614735179 := by
  apply lucas_primality 1533073286664614735179 (2 : ZMod 1533073286664614735179)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (139, 1), (359, 1), (929, 1), (3581, 1), (6197, 1), (248371, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (139, 1), (359, 1), (929, 1), (3581, 1), (6197, 1), (248371, 1)] : List FactorBlock).map factorBlockValue).prod) = 1533073286664614735179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_139
      · exact prime_oneHundredFiftyTwoET_359
      · exact prime_oneHundredFiftyTwoET_929
      · exact prime_oneHundredFiftyTwoET_3581
      · exact prime_oneHundredFiftyTwoET_6197
      · exact prime_oneHundredFiftyTwoET_248371
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1533073286664614735179) ^ 766536643332307367589 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 511024428888204911726 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 11029304220608739102 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 4270399127199483942 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 1650240351630371082 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 428113176951861138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 247389589586027874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1533073286664614735179) ^ 6172513242949518 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3456700946195018360381 : Nat.Prime 3456700946195018360381 := by
  apply lucas_primality 3456700946195018360381 (2 : ZMod 3456700946195018360381)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (2549, 1), (104113, 1), (116747, 1), (5578421, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (2549, 1), (104113, 1), (116747, 1), (5578421, 1)] : List FactorBlock).map factorBlockValue).prod) = 3456700946195018360381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_2549
      · exact prime_oneHundredFiftyTwoET_104113
      · exact prime_oneHundredFiftyTwoET_116747
      · exact prime_oneHundredFiftyTwoET_5578421
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3456700946195018360381) ^ 1728350473097509180190 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3456700946195018360381) ^ 691340189239003672076 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3456700946195018360381) ^ 1356100802744220620 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3456700946195018360381) ^ 33201434462507260 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3456700946195018360381) ^ 29608477701311540 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3456700946195018360381) ^ 619655803352780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_3582723846489009062341 : Nat.Prime 3582723846489009062341 := by
  apply lucas_primality 3582723846489009062341 (2 : ZMod 3582723846489009062341)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (23, 1), (53, 1), (115461013, 1), (424251137, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (23, 1), (53, 1), (115461013, 1), (424251137, 1)] : List FactorBlock).map factorBlockValue).prod) = 3582723846489009062341 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_23
      · exact prime_oneHundredFiftyTwoET_53
      · exact prime_oneHundredFiftyTwoET_115461013
      · exact prime_oneHundredFiftyTwoET_424251137
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3582723846489009062341) ^ 1791361923244504531170 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 1194241282163003020780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 716544769297801812468 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 155770602021261263580 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 67598563141302057780 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 31029728160180 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 3582723846489009062341) ^ 8444818490820 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_7162659520914713705041 : Nat.Prime 7162659520914713705041 := by
  apply lucas_primality 7162659520914713705041 (7 : ZMod 7162659520914713705041)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (17, 1), (1755553804145763163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (17, 1), (1755553804145763163, 1)] : List FactorBlock).map factorBlockValue).prod) = 7162659520914713705041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_17
      · exact prime_oneHundredFiftyTwoET_1755553804145763163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 7162659520914713705041) ^ 3581329760457356852520 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162659520914713705041) ^ 2387553173638237901680 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162659520914713705041) ^ 1432531904182942741008 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162659520914713705041) ^ 421332912994983159120 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (7 : ZMod 7162659520914713705041) ^ 4080 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_7488998344362023941087 : Nat.Prime 7488998344362023941087 := by
  apply lucas_primality 7488998344362023941087 (3 : ZMod 7488998344362023941087)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (3515265851, 1), (118356756277, 1)] : List FactorBlock).map factorBlockValue).prod) = 7488998344362023941087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_3515265851
      · exact prime_oneHundredFiftyTwoET_118356756277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 7488998344362023941087) ^ 3744499172181011970543 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2496332781454007980362 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 2130421612986 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 7488998344362023941087) ^ 63274785318 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_10909611845244380568449 : Nat.Prime 10909611845244380568449 := by
  apply lucas_primality 10909611845244380568449 (3 : ZMod 10909611845244380568449)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (157, 1), (66708619, 1), (8138000777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (157, 1), (66708619, 1), (8138000777, 1)] : List FactorBlock).map factorBlockValue).prod) = 10909611845244380568449 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_157
      · exact prime_oneHundredFiftyTwoET_66708619
      · exact prime_oneHundredFiftyTwoET_8138000777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 10909611845244380568449) ^ 5454805922622190284224 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 69487973536588411264 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 163541263614592 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 10909611845244380568449) ^ 1340576407424 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_46305000319161153277439 : Nat.Prime 46305000319161153277439 := by
  apply lucas_primality 46305000319161153277439 (14 : ZMod 46305000319161153277439)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (67, 1), (229, 1), (49667, 1), (30382232469499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (67, 1), (229, 1), (49667, 1), (30382232469499, 1)] : List FactorBlock).map factorBlockValue).prod) = 46305000319161153277439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_67
      · exact prime_oneHundredFiftyTwoET_229
      · exact prime_oneHundredFiftyTwoET_49667
      · exact prime_oneHundredFiftyTwoET_30382232469499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 46305000319161153277439) ^ 23152500159580576638719 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 46305000319161153277439) ^ 691119407748673929514 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 46305000319161153277439) ^ 202205241568389315622 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 46305000319161153277439) ^ 932309185559046314 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (14 : ZMod 46305000319161153277439) ^ 1524081562 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_50767716164439434687941 : Nat.Prime 50767716164439434687941 := by
  apply lucas_primality 50767716164439434687941 (18 : ZMod 50767716164439434687941)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (157, 1), (2213, 1), (347902276004377, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (157, 1), (2213, 1), (347902276004377, 1)] : List FactorBlock).map factorBlockValue).prod) = 50767716164439434687941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_7
      · exact prime_oneHundredFiftyTwoET_157
      · exact prime_oneHundredFiftyTwoET_2213
      · exact prime_oneHundredFiftyTwoET_347902276004377
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (18 : ZMod 50767716164439434687941) ^ 25383858082219717343970 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 16922572054813144895980 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 10153543232887886937588 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 7252530880634204955420 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 323361249455028246420 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 22940676079728619380 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (18 : ZMod 50767716164439434687941) ^ 145925220 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_51204986670124603892827 : Nat.Prime 51204986670124603892827 := by
  apply lucas_primality 51204986670124603892827 (2 : ZMod 51204986670124603892827)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (3923, 1), (46477, 1), (143138630863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (3923, 1), (46477, 1), (143138630863, 1)] : List FactorBlock).map factorBlockValue).prod) = 51204986670124603892827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_109
      · exact prime_oneHundredFiftyTwoET_3923
      · exact prime_oneHundredFiftyTwoET_46477
      · exact prime_oneHundredFiftyTwoET_143138630863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 51204986670124603892827) ^ 25602493335062301946413 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51204986670124603892827) ^ 17068328890041534630942 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51204986670124603892827) ^ 469770519909400035714 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51204986670124603892827) ^ 13052507435667755262 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51204986670124603892827) ^ 1101727449493827138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 51204986670124603892827) ^ 357730029702 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_85951914250976564460493 : Nat.Prime 85951914250976564460493 := by
  apply lucas_primality 85951914250976564460493 (5 : ZMod 85951914250976564460493)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7162659520914713705041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7162659520914713705041, 1)] : List FactorBlock).map factorBlockValue).prod) = 85951914250976564460493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_7162659520914713705041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 85951914250976564460493) ^ 42975957125488282230246 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 85951914250976564460493) ^ 28650638083658854820164 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (5 : ZMod 85951914250976564460493) ^ 12 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_248973811147188702642113 : Nat.Prime 248973811147188702642113 := by
  apply lucas_primality 248973811147188702642113 (3 : ZMod 248973811147188702642113)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (509, 1), (364759, 1), (902477, 1), (23217409, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (509, 1), (364759, 1), (902477, 1), (23217409, 1)] : List FactorBlock).map factorBlockValue).prod) = 248973811147188702642113 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_509
      · exact prime_oneHundredFiftyTwoET_364759
      · exact prime_oneHundredFiftyTwoET_902477
      · exact prime_oneHundredFiftyTwoET_23217409
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 248973811147188702642113) ^ 124486905573594351321056 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 248973811147188702642113) ^ 489143047440449317568 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 248973811147188702642113) ^ 682570714217301568 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 248973811147188702642113) ^ 275878289582104256 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 248973811147188702642113) ^ 10723582943608768 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_551083790156884719947153 : Nat.Prime 551083790156884719947153 := by
  apply lucas_primality 551083790156884719947153 (3 : ZMod 551083790156884719947153)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (192667, 1), (1592653, 1), (112245555847, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (192667, 1), (1592653, 1), (112245555847, 1)] : List FactorBlock).map factorBlockValue).prod) = 551083790156884719947153 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_192667
      · exact prime_oneHundredFiftyTwoET_1592653
      · exact prime_oneHundredFiftyTwoET_112245555847
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 551083790156884719947153) ^ 275541895078442359973576 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 551083790156884719947153) ^ 2860291540102273456 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 551083790156884719947153) ^ 346016232133983184 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 551083790156884719947153) ^ 4909626808816 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_721937033519319496150277 : Nat.Prime 721937033519319496150277 := by
  apply lucas_primality 721937033519319496150277 (2 : ZMod 721937033519319496150277)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (68767, 1), (2624576590222488607, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (68767, 1), (2624576590222488607, 1)] : List FactorBlock).map factorBlockValue).prod) = 721937033519319496150277 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_68767
      · exact prime_oneHundredFiftyTwoET_2624576590222488607
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 721937033519319496150277) ^ 360968516759659748075138 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 721937033519319496150277) ^ 10498306360889954428 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 721937033519319496150277) ^ 275068 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1954840379249293022601677 : Nat.Prime 1954840379249293022601677 := by
  apply lucas_primality 1954840379249293022601677 (2 : ZMod 1954840379249293022601677)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (373, 1), (125933891, 1), (10403988322733, 1)] : List FactorBlock).map factorBlockValue).prod) = 1954840379249293022601677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_373
      · exact prime_oneHundredFiftyTwoET_125933891
      · exact prime_oneHundredFiftyTwoET_10403988322733
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1954840379249293022601677) ^ 977420189624646511300838 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 5240858925601321776412 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 15522750577517636 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1954840379249293022601677) ^ 187893365372 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_4362290724205097924061827 : Nat.Prime 4362290724205097924061827 := by
  apply lucas_primality 4362290724205097924061827 (2 : ZMod 4362290724205097924061827)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (9811, 1), (3131215697962690573, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (9811, 1), (3131215697962690573, 1)] : List FactorBlock).map factorBlockValue).prod) = 4362290724205097924061827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_71
      · exact prime_oneHundredFiftyTwoET_9811
      · exact prime_oneHundredFiftyTwoET_3131215697962690573
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4362290724205097924061827) ^ 2181145362102548962030913 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362290724205097924061827) ^ 61440714425423914423406 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362290724205097924061827) ^ 444632629110702061366 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 4362290724205097924061827) ^ 1393162 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_5819448393252234746817583 : Nat.Prime 5819448393252234746817583 := by
  apply lucas_primality 5819448393252234746817583 (17 : ZMod 5819448393252234746817583)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1451, 1), (99907, 1), (53321713, 1), (125476717, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1451, 1), (99907, 1), (53321713, 1), (125476717, 1)] : List FactorBlock).map factorBlockValue).prod) = 5819448393252234746817583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_1451
      · exact prime_oneHundredFiftyTwoET_99907
      · exact prime_oneHundredFiftyTwoET_53321713
      · exact prime_oneHundredFiftyTwoET_125476717
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 5819448393252234746817583) ^ 2909724196626117373408791 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 5819448393252234746817583) ^ 1939816131084078248939194 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 5819448393252234746817583) ^ 4010646721745165228682 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 5819448393252234746817583) ^ 58248655181841460026 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 5819448393252234746817583) ^ 109138436592467214 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 5819448393252234746817583) ^ 46378710986295846 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_6120519273309117842775347 : Nat.Prime 6120519273309117842775347 := by
  apply lucas_primality 6120519273309117842775347 (2 : ZMod 6120519273309117842775347)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (59, 1), (91243, 1), (51678990468932339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (59, 1), (91243, 1), (51678990468932339, 1)] : List FactorBlock).map factorBlockValue).prod) = 6120519273309117842775347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_59
      · exact prime_oneHundredFiftyTwoET_91243
      · exact prime_oneHundredFiftyTwoET_51678990468932339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 6120519273309117842775347) ^ 3060259636654558921387673 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 6120519273309117842775347) ^ 556410843028101622070486 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 6120519273309117842775347) ^ 103737614801849454962294 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 6120519273309117842775347) ^ 67079329628674176022 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 6120519273309117842775347) ^ 118433414 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_14438740670386389923005541 : Nat.Prime 14438740670386389923005541 := by
  apply lucas_primality 14438740670386389923005541 (2 : ZMod 14438740670386389923005541)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (721937033519319496150277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (721937033519319496150277, 1)] : List FactorBlock).map factorBlockValue).prod) = 14438740670386389923005541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_721937033519319496150277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 14438740670386389923005541) ^ 7219370335193194961502770 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14438740670386389923005541) ^ 2887748134077277984601108 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 14438740670386389923005541) ^ 20 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_15105032057126082960555347 : Nat.Prime 15105032057126082960555347 := by
  apply lucas_primality 15105032057126082960555347 (2 : ZMod 15105032057126082960555347)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (10729, 1), (703934758930286278337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (10729, 1), (703934758930286278337, 1)] : List FactorBlock).map factorBlockValue).prod) = 15105032057126082960555347 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_10729
      · exact prime_oneHundredFiftyTwoET_703934758930286278337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 15105032057126082960555347) ^ 7552516028563041480277673 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 15105032057126082960555347) ^ 1407869517860572556674 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 15105032057126082960555347) ^ 21458 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_50922234736080761967052129 : Nat.Prime 50922234736080761967052129 := by
  apply lucas_primality 50922234736080761967052129 (17 : ZMod 50922234736080761967052129)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (11, 1), (44059, 1), (1094482698133098257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (11, 1), (44059, 1), (1094482698133098257, 1)] : List FactorBlock).map factorBlockValue).prod) = 50922234736080761967052129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_11
      · exact prime_oneHundredFiftyTwoET_44059
      · exact prime_oneHundredFiftyTwoET_1094482698133098257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 50922234736080761967052129) ^ 25461117368040380983526064 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 50922234736080761967052129) ^ 16974078245360253989017376 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 50922234736080761967052129) ^ 4629294066916432906095648 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 50922234736080761967052129) ^ 1155773729228551759392 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (17 : ZMod 50922234736080761967052129) ^ 46526304 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_386461433083073137595111749 : Nat.Prime 386461433083073137595111749 := by
  apply lucas_primality 386461433083073137595111749 (2 : ZMod 386461433083073137595111749)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (19, 1), (43, 1), (52919, 1), (2515757, 1), (22776090853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (19, 1), (43, 1), (52919, 1), (2515757, 1), (22776090853, 1)] : List FactorBlock).map factorBlockValue).prod) = 386461433083073137595111749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_3
      · exact prime_oneHundredFiftyTwoET_13
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_43
      · exact prime_oneHundredFiftyTwoET_52919
      · exact prime_oneHundredFiftyTwoET_2515757
      · exact prime_oneHundredFiftyTwoET_22776090853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 386461433083073137595111749) ^ 193230716541536568797555874 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 128820477694357712531703916 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 29727802544851779815008596 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 20340075425424901978690092 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 8987475187978445060351436 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 7302886167219205532892 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 153616360039174346964 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 386461433083073137595111749) ^ 16967856142537716 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_931111742920357559490813281 : Nat.Prime 931111742920357559490813281 := by
  apply lucas_primality 931111742920357559490813281 (3 : ZMod 931111742920357559490813281)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (5819448393252234746817583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (5819448393252234746817583, 1)] : List FactorBlock).map factorBlockValue).prod) = 931111742920357559490813281 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_5819448393252234746817583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 931111742920357559490813281) ^ 465555871460178779745406640 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 931111742920357559490813281) ^ 186222348584071511898162656 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 931111742920357559490813281) ^ 160 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_1497538053196908408181058027 : Nat.Prime 1497538053196908408181058027 := by
  apply lucas_primality 1497538053196908408181058027 (2 : ZMod 1497538053196908408181058027)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1703297, 1), (4959861037, 1), (88631475817, 1)] : List FactorBlock).map factorBlockValue).prod) = 1497538053196908408181058027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1703297
      · exact prime_oneHundredFiftyTwoET_4959861037
      · exact prime_oneHundredFiftyTwoET_88631475817
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1497538053196908408181058027) ^ 748769026598454204090529013 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 879199607113092084458 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 301931453729337298 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 1497538053196908408181058027) ^ 16896232849477978 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2246307079795362612271587041 : Nat.Prime 2246307079795362612271587041 := by
  apply lucas_primality 2246307079795362612271587041 (6 : ZMod 2246307079795362612271587041)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 2246307079795362612271587041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_19
      · exact prime_oneHundredFiftyTwoET_171401
      · exact prime_oneHundredFiftyTwoET_714027719
      · exact prime_oneHundredFiftyTwoET_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 2246307079795362612271587041) ^ 1123153539897681306135793520 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 449261415959072522454317408 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 118226688410282242751136160 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 13105565777302131331040 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 3145966213946608160 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (6 : ZMod 2246307079795362612271587041) ^ 372050597795529760 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_2604414005559840709880100917 : Nat.Prime 2604414005559840709880100917 := by
  apply lucas_primality 2604414005559840709880100917 (2 : ZMod 2604414005559840709880100917)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17002049, 1), (38295590219153007821, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17002049, 1), (38295590219153007821, 1)] : List FactorBlock).map factorBlockValue).prod) = 2604414005559840709880100917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_17002049
      · exact prime_oneHundredFiftyTwoET_38295590219153007821
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2604414005559840709880100917) ^ 1302207002779920354940050458 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2604414005559840709880100917) ^ 153182360876612031284 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 2604414005559840709880100917) ^ 68008196 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_11980304425575267265448464217 : Nat.Prime 11980304425575267265448464217 := by
  apply lucas_primality 11980304425575267265448464217 (3 : ZMod 11980304425575267265448464217)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 11980304425575267265448464217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1497538053196908408181058027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 11980304425575267265448464217) ^ 5990152212787633632724232108 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (3 : ZMod 11980304425575267265448464217) ^ 8 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_29950761063938168163621160541 : Nat.Prime 29950761063938168163621160541 := by
  apply lucas_primality 29950761063938168163621160541 (2 : ZMod 29950761063938168163621160541)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 29950761063938168163621160541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_5
      · exact prime_oneHundredFiftyTwoET_1497538053196908408181058027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 29950761063938168163621160541) ^ 14975380531969084081810580270 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 29950761063938168163621160541) ^ 5990152212787633632724232108 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 29950761063938168163621160541) ^ 20 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem prime_oneHundredFiftyTwoET_44926141595907252245431740803 : Nat.Prime 44926141595907252245431740803 := by
  apply lucas_primality 44926141595907252245431740803 (2 : ZMod 44926141595907252245431740803)
  · rw [← oneHundredFiftyTwoETFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) = 44926141595907252245431740803 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredFiftyTwoET_2
      · exact prime_oneHundredFiftyTwoET_1489
      · exact prime_oneHundredFiftyTwoET_74197
      · exact prime_oneHundredFiftyTwoET_125471
      · exact prime_oneHundredFiftyTwoET_28901293
      · exact prime_oneHundredFiftyTwoET_56069599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 44926141595907252245431740803) ^ 22463070797953626122715870401 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 30172022562731532737026018 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 605498087468593773945466 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 358059962827324658649662 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 1554468223823316563914 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide
    · change (2 : ZMod 44926141595907252245431740803) ^ 801256695199608119998 ≠ 1
      rw [← oneHundredFiftyTwoETFastPow_eq_pow]
      decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963200 : Nat.totient 179704566383629008981726963200 = 68098175112098698832388096000 := by
  rw [← show ((([(2, 9), (5, 2), (19, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963200 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_171401, prime_oneHundredFiftyTwoET_714027719, prime_oneHundredFiftyTwoET_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963201 : Nat.totient 179704566383629008981726963201 = 118905190559486971462128948864 := by
  rw [← show ((([(3, 1), (137, 1), (5087, 1), (85951914250976564460493, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963201 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_137, prime_oneHundredFiftyTwoET_5087, prime_oneHundredFiftyTwoET_85951914250976564460493]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963202 : Nat.totient 179704566383629008981726963202 = 76461955304765991440207902272 := by
  rw [← show ((([(2, 1), (7, 1), (139, 1), (358279, 1), (233755999, 1), (1102635976397, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963202 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_139, prime_oneHundredFiftyTwoET_358279, prime_oneHundredFiftyTwoET_233755999, prime_oneHundredFiftyTwoET_1102635976397]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963203 : Nat.totient 179704566383629008981726963203 = 179704492310639773910386445256 := by
  rw [← show ((([(2426107, 1), (116376108847, 1), (636480833207, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963203 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2426107, prime_oneHundredFiftyTwoET_116376108847, prime_oneHundredFiftyTwoET_636480833207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963204 : Nat.totient 179704566383629008981726963204 = 57297104752304556330401351680 := by
  rw [← show ((([(2, 2), (3, 1), (23, 1), (17002049, 1), (38295590219153007821, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963204 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_23, prime_oneHundredFiftyTwoET_17002049, prime_oneHundredFiftyTwoET_38295590219153007821]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963205 : Nat.totient 179704566383629008981726963205 = 143332408923659701474772413440 := by
  rw [← show ((([(5, 1), (337, 1), (30853, 1), (3456700946195018360381, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963205 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_337, prime_oneHundredFiftyTwoET_30853, prime_oneHundredFiftyTwoET_3456700946195018360381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963206 : Nat.totient 179704566383629008981726963206 = 89850791951502365976393680640 := by
  rw [← show ((([(2, 1), (60257, 1), (1005543181, 1), (1482930802749359, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963206 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_60257, prime_oneHundredFiftyTwoET_1005543181, prime_oneHundredFiftyTwoET_1482930802749359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963207 : Nat.totient 179704566383629008981726963207 = 116419452616450994346098380800 := by
  rw [← show ((([(3, 4), (43, 1), (197, 1), (33457, 1), (7828028820389715601, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963207 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_43, prime_oneHundredFiftyTwoET_197, prime_oneHundredFiftyTwoET_33457, prime_oneHundredFiftyTwoET_7828028820389715601]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963208 : Nat.totient 179704566383629008981726963208 = 89790008626284063232589475840 := by
  rw [← show ((([(2, 3), (1489, 1), (74197, 1), (125471, 1), (28901293, 1), (56069599, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963208 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_1489, prime_oneHundredFiftyTwoET_74197, prime_oneHundredFiftyTwoET_125471, prime_oneHundredFiftyTwoET_28901293, prime_oneHundredFiftyTwoET_56069599]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963209 : Nat.totient 179704566383629008981726963209 = 154027247092927902919630701072 := by
  rw [← show ((([(7, 1), (46187, 1), (80923, 1), (6868617687843709687, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963209 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_46187, prime_oneHundredFiftyTwoET_80923, prime_oneHundredFiftyTwoET_6868617687843709687]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963210 : Nat.totient 179704566383629008981726963210 = 40213609260269106478840381440 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (13, 1), (99779807873, 1), (419816165275813, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963210 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_99779807873, prime_oneHundredFiftyTwoET_419816165275813]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963211 : Nat.totient 179704566383629008981726963211 = 176327202572432643174923813760 := by
  rw [← show ((([(103, 1), (109, 1), (1734429894853, 1), (9228659865181, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963211 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_103, prime_oneHundredFiftyTwoET_109, prime_oneHundredFiftyTwoET_1734429894853, prime_oneHundredFiftyTwoET_9228659865181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963212 : Nat.totient 179704566383629008981726963212 = 89852283191814504490863481604 := by
  rw [← show ((([(2, 2), (44926141595907252245431740803, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963212 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_44926141595907252245431740803]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963213 : Nat.totient 179704566383629008981726963213 = 118280760182828715503416320000 := by
  rw [← show ((([(3, 1), (101, 1), (571, 1), (929, 1), (128389, 1), (8708369456992421, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963213 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_101, prime_oneHundredFiftyTwoET_571, prime_oneHundredFiftyTwoET_929, prime_oneHundredFiftyTwoET_128389, prime_oneHundredFiftyTwoET_8708369456992421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963214 : Nat.totient 179704566383629008981726963214 = 89738111097218824364471519232 := by
  rw [← show ((([(2, 1), (787, 1), (61132733, 1), (1867585842648450817, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963214 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_787, prime_oneHundredFiftyTwoET_61132733, prime_oneHundredFiftyTwoET_1867585842648450817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963215 : Nat.totient 179704566383629008981726963215 = 135267205480674140223131443200 := by
  rw [← show ((([(5, 1), (17, 1), (4561, 1), (13399, 1), (34594553351042402261, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963215 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_4561, prime_oneHundredFiftyTwoET_13399, prime_oneHundredFiftyTwoET_34594553351042402261]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963216 : Nat.totient 179704566383629008981726963216 = 51084076039383009102294528000 := by
  rw [← show ((([(2, 4), (3, 2), (7, 1), (277, 1), (743, 1), (9091, 1), (201451, 1), (472986682277, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963216 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_277, prime_oneHundredFiftyTwoET_743, prime_oneHundredFiftyTwoET_9091, prime_oneHundredFiftyTwoET_201451, prime_oneHundredFiftyTwoET_472986682277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963217 : Nat.totient 179704566383629008981726963217 = 175881064971204947739503398800 := by
  rw [← show ((([(47, 1), (37404377760941, 1), (102220692905371, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963217 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_47, prime_oneHundredFiftyTwoET_37404377760941, prime_oneHundredFiftyTwoET_102220692905371]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963218 : Nat.totient 179704566383629008981726963218 = 89851395671204037599642941440 := by
  rw [← show ((([(2, 1), (139303, 1), (370511, 1), (1740874811875804673, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963218 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_139303, prime_oneHundredFiftyTwoET_370511, prime_oneHundredFiftyTwoET_1740874811875804673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963219 : Nat.totient 179704566383629008981726963219 = 111898918696799447221457256192 := by
  rw [← show ((([(3, 1), (19, 1), (89, 1), (347, 1), (2755243, 1), (37051420944511243, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963219 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_89, prime_oneHundredFiftyTwoET_347, prime_oneHundredFiftyTwoET_2755243, prime_oneHundredFiftyTwoET_37051420944511243]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963220 : Nat.totient 179704566383629008981726963220 = 71881618199082079427819568000 := by
  rw [← show ((([(2, 2), (5, 1), (470501, 1), (1293367, 1), (14765453512034683, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963220 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_470501, prime_oneHundredFiftyTwoET_1293367, prime_oneHundredFiftyTwoET_14765453512034683]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963221 : Nat.totient 179704566383629008981726963221 = 162716816007029648047714560000 := by
  rw [← show ((([(11, 1), (251, 1), (1565569, 1), (41573873765184175469, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963221 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_251, prime_oneHundredFiftyTwoET_1565569, prime_oneHundredFiftyTwoET_41573873765184175469]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963222 : Nat.totient 179704566383629008981726963222 = 59901522127875241451474538312 := by
  rw [← show ((([(2, 1), (3, 1), (61654569369979, 1), (485783314521403, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963222 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_61654569369979, prime_oneHundredFiftyTwoET_485783314521403]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963223 : Nat.totient 179704566383629008981726963223 = 134308425936263767048396800000 := by
  rw [← show ((([(7, 1), (13, 1), (31, 1), (67, 1), (227, 1), (241, 1), (1721, 1), (72794101, 1), (138727087, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963223 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_31, prime_oneHundredFiftyTwoET_67, prime_oneHundredFiftyTwoET_227, prime_oneHundredFiftyTwoET_241, prime_oneHundredFiftyTwoET_1721, prime_oneHundredFiftyTwoET_72794101, prime_oneHundredFiftyTwoET_138727087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963224 : Nat.totient 179704566383629008981726963224 = 86527416180050738708668088320 := by
  rw [← show ((([(2, 3), (29, 1), (383, 1), (101080961, 1), (20007968354627489, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963224 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_29, prime_oneHundredFiftyTwoET_383, prime_oneHundredFiftyTwoET_101080961, prime_oneHundredFiftyTwoET_20007968354627489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963225 : Nat.totient 179704566383629008981726963225 = 94503983386692655221701760000 := by
  rw [← show ((([(3, 2), (5, 2), (73, 1), (3701, 1), (289317307, 1), (10217866768471, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963225 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_73, prime_oneHundredFiftyTwoET_3701, prime_oneHundredFiftyTwoET_289317307, prime_oneHundredFiftyTwoET_10217866768471]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963226 : Nat.totient 179704566383629008981726963226 = 86650180776946759768079155200 := by
  rw [← show ((([(2, 1), (37, 1), (113, 1), (371414407073, 1), (57861568703801, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963226 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_37, prime_oneHundredFiftyTwoET_113, prime_oneHundredFiftyTwoET_371414407073, prime_oneHundredFiftyTwoET_57861568703801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963227 : Nat.totient 179704566383629008981726963227 = 171891266295302693022115448832 := by
  rw [← show ((([(23, 1), (2977717, 1), (497172713, 1), (5277649833569, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963227 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_23, prime_oneHundredFiftyTwoET_2977717, prime_oneHundredFiftyTwoET_497172713, prime_oneHundredFiftyTwoET_5277649833569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963228 : Nat.totient 179704566383629008981726963228 = 58440509392910707557740544000 := by
  rw [← show ((([(2, 2), (3, 1), (41, 1), (419501118209, 1), (870684648627301, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963228 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_41, prime_oneHundredFiftyTwoET_419501118209, prime_oneHundredFiftyTwoET_870684648627301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963229 : Nat.totient 179704566383629008981726963229 = 176626763415602807820821793216 := by
  rw [← show ((([(59, 1), (5527, 1), (551083790156884719947153, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963229 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_59, prime_oneHundredFiftyTwoET_5527, prime_oneHundredFiftyTwoET_551083790156884719947153]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963230 : Nat.totient 179704566383629008981726963230 = 61196169045817971839808921600 := by
  rw [← show ((([(2, 1), (5, 1), (7, 1), (163, 1), (2053, 1), (6823, 1), (1809937, 1), (621220372301, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963230 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_163, prime_oneHundredFiftyTwoET_2053, prime_oneHundredFiftyTwoET_6823, prime_oneHundredFiftyTwoET_1809937, prime_oneHundredFiftyTwoET_621220372301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963231 : Nat.totient 179704566383629008981726963231 = 119463658861166808012101249280 := by
  rw [← show ((([(3, 1), (353, 1), (1288148676091, 1), (131733782284399, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963231 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_353, prime_oneHundredFiftyTwoET_1288148676091, prime_oneHundredFiftyTwoET_131733782284399]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963232 : Nat.totient 179704566383629008981726963232 = 76492632059658994236242042880 := by
  rw [← show ((([(2, 5), (11, 2), (17, 1), (199, 1), (193897349, 1), (70753820440643, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963232 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_199, prime_oneHundredFiftyTwoET_193897349, prime_oneHundredFiftyTwoET_70753820440643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963233 : Nat.totient 179704566383629008981726963233 = 178773454640708651422236149760 := by
  rw [← show ((([(193, 1), (931111742920357559490813281, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963233 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_193, prime_oneHundredFiftyTwoET_931111742920357559490813281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963234 : Nat.totient 179704566383629008981726963234 = 59748513803830621634563816704 := by
  rw [← show ((([(2, 1), (3, 3), (509, 1), (1693, 1), (5316797, 1), (726340956728039, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963234 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_509, prime_oneHundredFiftyTwoET_1693, prime_oneHundredFiftyTwoET_5316797, prime_oneHundredFiftyTwoET_726340956728039]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963235 : Nat.totient 179704566383629008981726963235 = 143560883479390901399954125440 := by
  rw [← show ((([(5, 1), (709, 1), (7952358461, 1), (6374511739318903, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963235 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_709, prime_oneHundredFiftyTwoET_7952358461, prime_oneHundredFiftyTwoET_6374511739318903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963236 : Nat.totient 179704566383629008981726963236 = 82640860907359258097721244800 := by
  rw [← show ((([(2, 2), (13, 1), (283, 1), (12479, 1), (9130651, 1), (107173596754699, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963236 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_283, prime_oneHundredFiftyTwoET_12479, prime_oneHundredFiftyTwoET_9130651, prime_oneHundredFiftyTwoET_107173596754699]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963237 : Nat.totient 179704566383629008981726963237 = 100750807870944372340291572480 := by
  rw [← show ((([(3, 1), (7, 2), (53, 1), (426333337, 1), (54102410473047011, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963237 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_53, prime_oneHundredFiftyTwoET_426333337, prime_oneHundredFiftyTwoET_54102410473047011]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963238 : Nat.totient 179704566383629008981726963238 = 85111957424745665939386854720 := by
  rw [← show ((([(2, 1), (19, 1), (7561, 1), (2416168199, 1), (258862483991359, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963238 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_7561, prime_oneHundredFiftyTwoET_2416168199, prime_oneHundredFiftyTwoET_258862483991359]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963239 : Nat.totient 179704566383629008981726963239 = 179704566383623559987439014400 := by
  rw [← show ((([(33181458080039, 1), (5415812829868801, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963239 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_33181458080039, prime_oneHundredFiftyTwoET_5415812829868801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963240 : Nat.totient 179704566383629008981726963240 = 47921217702301069061793856832 := by
  rw [← show ((([(2, 3), (3, 1), (5, 1), (1497538053196908408181058027, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963240 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_1497538053196908408181058027]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963241 : Nat.totient 179704566383629008981726963241 = 179653644148892928219759907584 := by
  rw [← show ((([(3529, 1), (50922234736080761967052129, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963241 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3529, prime_oneHundredFiftyTwoET_50922234736080761967052129]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963242 : Nat.totient 179704566383629008981726963242 = 89718773058257873260163637120 := by
  rw [← show ((([(2, 1), (673, 1), (1645619411, 1), (81130593224918807, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963242 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_673, prime_oneHundredFiftyTwoET_1645619411, prime_oneHundredFiftyTwoET_81130593224918807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963243 : Nat.totient 179704566383629008981726963243 = 108910466090004292808960785920 := by
  rw [← show ((([(3, 2), (11, 1), (78233, 1), (615208637, 1), (37714774023317, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963243 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_78233, prime_oneHundredFiftyTwoET_615208637, prime_oneHundredFiftyTwoET_37714774023317]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963244 : Nat.totient 179704566383629008981726963244 = 76643801626284978231953479680 := by
  rw [← show ((([(2, 2), (7, 1), (211, 1), (21227, 1), (49529, 1), (52147, 1), (96589, 1), (5743987, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963244 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_211, prime_oneHundredFiftyTwoET_21227, prime_oneHundredFiftyTwoET_49529, prime_oneHundredFiftyTwoET_52147, prime_oneHundredFiftyTwoET_96589, prime_oneHundredFiftyTwoET_5743987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963245 : Nat.totient 179704566383629008981726963245 = 143035528402082657007118969344 := by
  rw [← show ((([(5, 1), (229, 1), (1433, 1), (317599, 1), (344848474771720643, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963245 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_229, prime_oneHundredFiftyTwoET_1433, prime_oneHundredFiftyTwoET_317599, prime_oneHundredFiftyTwoET_344848474771720643]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963246 : Nat.totient 179704566383629008981726963246 = 59901522127876336327242321080 := by
  rw [← show ((([(2, 1), (3, 1), (29950761063938168163621160541, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963246 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_29950761063938168163621160541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963247 : Nat.totient 179704566383629008981726963247 = 179704566383540046491352074400 := by
  rw [← show ((([(2020049643697, 1), (88960470325245151, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963247 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2020049643697, prime_oneHundredFiftyTwoET_88960470325245151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963248 : Nat.totient 179704566383629008981726963248 = 89852025027164929133691340800 := by
  rw [← show ((([(2, 4), (352333, 1), (28581281, 1), (1115331887063311, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963248 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_352333, prime_oneHundredFiftyTwoET_28581281, prime_oneHundredFiftyTwoET_1115331887063311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963249 : Nat.totient 179704566383629008981726963249 = 104082277453942195298493517824 := by
  rw [← show ((([(3, 1), (13, 1), (17, 1), (23983727, 1), (104320037, 1), (108333102277, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963249 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_23983727, prime_oneHundredFiftyTwoET_104320037, prime_oneHundredFiftyTwoET_108333102277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963250 : Nat.totient 179704566383629008981726963250 = 65950078877005591876608000000 := by
  rw [← show ((([(2, 1), (5, 3), (23, 1), (43, 1), (71, 1), (263, 1), (9341, 1), (27241, 1), (324361, 1), (471589, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963250 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_23, prime_oneHundredFiftyTwoET_43, prime_oneHundredFiftyTwoET_71, prime_oneHundredFiftyTwoET_263, prime_oneHundredFiftyTwoET_9341, prime_oneHundredFiftyTwoET_27241, prime_oneHundredFiftyTwoET_324361, prime_oneHundredFiftyTwoET_471589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963251 : Nat.totient 179704566383629008981726963251 = 151488928963830238124847864480 := by
  rw [← show ((([(7, 1), (61, 1), (8219, 1), (51204986670124603892827, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963251 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_61, prime_oneHundredFiftyTwoET_8219, prime_oneHundredFiftyTwoET_51204986670124603892827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963252 : Nat.totient 179704566383629008981726963252 = 59901522127802579859620303232 := by
  rw [← show ((([(2, 2), (3, 2), (812260148269, 1), (6145560041686553, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963252 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_812260148269, prime_oneHundredFiftyTwoET_6145560041686553]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963253 : Nat.totient 179704566383629008981726963253 = 173500885931274508077992736768 := by
  rw [← show ((([(29, 1), (24889, 1), (248973811147188702642113, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963253 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_29, prime_oneHundredFiftyTwoET_24889, prime_oneHundredFiftyTwoET_248973811147188702642113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963254 : Nat.totient 179704566383629008981726963254 = 78942295817320627385366400000 := by
  rw [← show ((([(2, 1), (11, 1), (31, 1), (821, 1), (13903, 1), (16901, 1), (1365874058110169, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963254 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_31, prime_oneHundredFiftyTwoET_821, prime_oneHundredFiftyTwoET_13903, prime_oneHundredFiftyTwoET_16901, prime_oneHundredFiftyTwoET_1365874058110169]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963255 : Nat.totient 179704566383629008981726963255 = 95842435404602138123587713728 := by
  rw [← show ((([(3, 1), (5, 1), (11980304425575267265448464217, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963255 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_11980304425575267265448464217]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963256 : Nat.totient 179704566383629008981726963256 = 89844463830297507318773028960 := by
  rw [← show ((([(2, 3), (11491, 1), (1954840379249293022601677, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963256 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_11491, prime_oneHundredFiftyTwoET_1954840379249293022601677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963257 : Nat.totient 179704566383629008981726963257 = 170019691025125879820417850000 := by
  rw [← show ((([(19, 1), (751, 1), (3594403, 1), (3503795954666829551, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963257 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_751, prime_oneHundredFiftyTwoET_3594403, prime_oneHundredFiftyTwoET_3503795954666829551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963258 : Nat.totient 179704566383629008981726963258 = 50618183907896561335303641600 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (131, 1), (167, 1), (1753, 1), (1178711, 1), (94652655590939, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963258 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_131, prime_oneHundredFiftyTwoET_167, prime_oneHundredFiftyTwoET_1753, prime_oneHundredFiftyTwoET_1178711, prime_oneHundredFiftyTwoET_94652655590939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963259 : Nat.totient 179704566383629008981726963259 = 179689461351571882898766396016 := by
  rw [← show ((([(11897, 1), (15105032057126082960555347, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963259 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_11897, prime_oneHundredFiftyTwoET_15105032057126082960555347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963260 : Nat.totient 179704566383629008981726963260 = 71684907075546494707187654400 := by
  rw [← show ((([(2, 2), (5, 1), (479, 1), (1531, 1), (466649147, 1), (26255962099621, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963260 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_479, prime_oneHundredFiftyTwoET_1531, prime_oneHundredFiftyTwoET_466649147, prime_oneHundredFiftyTwoET_26255962099621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963261 : Nat.totient 179704566383629008981726963261 = 119803039903728320545053808704 := by
  rw [← show ((([(3, 3), (27528119, 1), (241779130672718629297, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963261 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_27528119, prime_oneHundredFiftyTwoET_241779130672718629297]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963262 : Nat.totient 179704566383629008981726963262 = 82412216642423016493005109248 := by
  rw [← show ((([(2, 1), (13, 1), (157, 1), (1201729, 1), (36633597620505094679, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963262 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_157, prime_oneHundredFiftyTwoET_1201729, prime_oneHundredFiftyTwoET_36633597620505094679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963263 : Nat.totient 179704566383629008981726963263 = 172730511381254280210116069760 := by
  rw [← show ((([(37, 1), (83, 1), (16333, 1), (3582723846489009062341, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963263 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_37, prime_oneHundredFiftyTwoET_83, prime_oneHundredFiftyTwoET_16333, prime_oneHundredFiftyTwoET_3582723846489009062341]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963264 : Nat.totient 179704566383629008981726963264 = 58521045153291024427941888000 := by
  rw [← show ((([(2, 6), (3, 1), (47, 1), (563, 1), (40771, 1), (283277, 1), (299281, 1), (10233161, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963264 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_47, prime_oneHundredFiftyTwoET_563, prime_oneHundredFiftyTwoET_40771, prime_oneHundredFiftyTwoET_283277, prime_oneHundredFiftyTwoET_299281, prime_oneHundredFiftyTwoET_10233161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963265 : Nat.totient 179704566383629008981726963265 = 110976676023777691188132853440 := by
  rw [← show ((([(5, 1), (7, 1), (11, 1), (107, 1), (4362290724205097924061827, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963265 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_107, prime_oneHundredFiftyTwoET_4362290724205097924061827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963266 : Nat.totient 179704566383629008981726963266 = 84566853462567256483955712576 := by
  rw [← show ((([(2, 1), (17, 1), (64742687, 1), (81637458498562347727, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963266 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_64742687, prime_oneHundredFiftyTwoET_81637458498562347727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963267 : Nat.totient 179704566383629008981726963267 = 119790803217206054418799071912 := by
  rw [← show ((([(3, 1), (9787, 1), (6120519273309117842775347, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963267 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_9787, prime_oneHundredFiftyTwoET_6120519273309117842775347]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963268 : Nat.totient 179704566383629008981726963268 = 88713210619052538715703589888 := by
  rw [← show ((([(2, 2), (79, 1), (52127, 1), (10909611845244380568449, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963268 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_79, prime_oneHundredFiftyTwoET_52127, prime_oneHundredFiftyTwoET_10909611845244380568449]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963269 : Nat.totient 179704566383629008981726963269 = 175105331850403386990065894400 := by
  rw [← show ((([(41, 1), (1609, 1), (1637, 1), (873043, 1), (1906052673410411, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963269 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_41, prime_oneHundredFiftyTwoET_1609, prime_oneHundredFiftyTwoET_1637, prime_oneHundredFiftyTwoET_873043, prime_oneHundredFiftyTwoET_1906052673410411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963270 : Nat.totient 179704566383629008981726963270 = 47653086204450723504795420672 := by
  rw [← show ((([(2, 1), (3, 2), (5, 1), (179, 1), (114773, 1), (97190505030529514209, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963270 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_179, prime_oneHundredFiftyTwoET_114773, prime_oneHundredFiftyTwoET_97190505030529514209]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963271 : Nat.totient 179704566383629008981726963271 = 179704520078628689820569804944 := by
  rw [← show ((([(3880889, 1), (46305000319161153277439, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963271 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3880889, prime_oneHundredFiftyTwoET_46305000319161153277439]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963272 : Nat.totient 179704566383629008981726963272 = 76994633294549819011700390400 := by
  rw [← show ((([(2, 3), (7, 1), (7817, 1), (9887, 1), (19403, 1), (2139920090441051, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963272 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_7817, prime_oneHundredFiftyTwoET_9887, prime_oneHundredFiftyTwoET_19403, prime_oneHundredFiftyTwoET_2139920090441051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963273 : Nat.totient 179704566383629008981726963273 = 114594216244632991234724440304 := by
  rw [← show ((([(3, 1), (23, 1), (2604414005559840709880100917, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963273 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_23, prime_oneHundredFiftyTwoET_2604414005559840709880100917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963274 : Nat.totient 179704566383629008981726963274 = 89851438643708515881579985440 := by
  rw [← show ((([(2, 1), (106391, 1), (309922603129, 1), (2725028037883, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963274 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_106391, prime_oneHundredFiftyTwoET_309922603129, prime_oneHundredFiftyTwoET_2725028037883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963275 : Nat.totient 179704566383629008981726963275 = 132704910332730920064469587840 := by
  rw [← show ((([(5, 2), (13, 1), (583350533, 1), (947864270373852739, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963275 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_583350533, prime_oneHundredFiftyTwoET_947864270373852739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963276 : Nat.totient 179704566383629008981726963276 = 51477183719686484517305088000 := by
  rw [← show ((([(2, 2), (3, 1), (11, 1), (19, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963276 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_461, prime_oneHundredFiftyTwoET_69997, prime_oneHundredFiftyTwoET_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963277 : Nat.totient 179704566383629008981726963277 = 178540914767187104468390880000 := by
  rw [← show ((([(181, 1), (1051, 1), (232171, 1), (4068832858225057777, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963277 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_181, prime_oneHundredFiftyTwoET_1051, prime_oneHundredFiftyTwoET_232171, prime_oneHundredFiftyTwoET_4068832858225057777]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963278 : Nat.totient 179704566383629008981726963278 = 89852283191806892014708898424 := by
  rw [← show ((([(2, 1), (11821650773203, 1), (7600654503810013, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963278 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_11821650773203, prime_oneHundredFiftyTwoET_7600654503810013]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963279 : Nat.totient 179704566383629008981726963279 = 102630923800418595907721183040 := by
  rw [← show ((([(3, 2), (7, 1), (1789, 1), (55813317187, 1), (28567378430231, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963279 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_1789, prime_oneHundredFiftyTwoET_55813317187, prime_oneHundredFiftyTwoET_28567378430231]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963280 : Nat.totient 179704566383629008981726963280 = 71881826553451603592690785280 := by
  rw [← show ((([(2, 4), (5, 1), (2246307079795362612271587041, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963280 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_2246307079795362612271587041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963281 : Nat.totient 179704566383629008981726963281 = 179447834042985438760506510960 := by
  rw [← show ((([(839, 1), (4219, 1), (50767716164439434687941, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963281 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_839, prime_oneHundredFiftyTwoET_4219, prime_oneHundredFiftyTwoET_50767716164439434687941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963282 : Nat.totient 179704566383629008981726963282 = 56924443396758866525720739840 := by
  rw [← show ((([(2, 1), (3, 1), (29, 1), (97, 1), (191, 1), (3767, 1), (123143, 1), (120170927531489, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963282 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_29, prime_oneHundredFiftyTwoET_97, prime_oneHundredFiftyTwoET_191, prime_oneHundredFiftyTwoET_3767, prime_oneHundredFiftyTwoET_123143, prime_oneHundredFiftyTwoET_120170927531489]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963283 : Nat.totient 179704566383629008981726963283 = 169133709537529824285228092160 := by
  rw [← show ((([(17, 1), (83611192864571, 1), (126428729024569, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963283 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_83611192864571, prime_oneHundredFiftyTwoET_126428729024569]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963284 : Nat.totient 179704566383629008981726963284 = 89852046621304518685888106496 := by
  rw [← show ((([(2, 2), (390989, 1), (20637977, 1), (72827129, 1), (76449433, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963284 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_390989, prime_oneHundredFiftyTwoET_20637977, prime_oneHundredFiftyTwoET_72827129, prime_oneHundredFiftyTwoET_76449433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963285 : Nat.totient 179704566383629008981726963285 = 92750743939937553022826819520 := by
  rw [← show ((([(3, 1), (5, 1), (31, 1), (386461433083073137595111749, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963285 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_31, prime_oneHundredFiftyTwoET_386461433083073137595111749]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963286 : Nat.totient 179704566383629008981726963286 = 76409815627684775472545317680 := by
  rw [← show ((([(2, 1), (7, 2), (127, 1), (14438740670386389923005541, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963286 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_127, prime_oneHundredFiftyTwoET_14438740670386389923005541]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963287 : Nat.totient 179704566383629008981726963287 = 163214364497486143591703255040 := by
  rw [← show ((([(11, 1), (1069, 1), (271969, 1), (56191330843355904697, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963287 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_1069, prime_oneHundredFiftyTwoET_271969, prime_oneHundredFiftyTwoET_56191330843355904697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963288 : Nat.totient 179704566383629008981726963288 = 54356151420498933880065676800 := by
  rw [← show ((([(2, 3), (3, 5), (13, 1), (59, 1), (143141, 1), (841983229614766891, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963288 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_59, prime_oneHundredFiftyTwoET_143141, prime_oneHundredFiftyTwoET_841983229614766891]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963289 : Nat.totient 179704566383629008981726963289 = 179704566383304260919027049524 := by
  rw [← show ((([(553367035063, 1), (324747509332878703, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963289 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_553367035063, prime_oneHundredFiftyTwoET_324747509332878703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963290 : Nat.totient 179704566383629008981726963290 = 69451899261795042578927827200 := by
  rw [← show ((([(2, 1), (5, 1), (53, 1), (67, 1), (3301, 1), (1533073286664614735179, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963290 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_53, prime_oneHundredFiftyTwoET_67, prime_oneHundredFiftyTwoET_3301, prime_oneHundredFiftyTwoET_1533073286664614735179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963291 : Nat.totient 179704566383629008981726963291 = 119788624525746823894823773824 := by
  rw [← show ((([(3, 1), (10957, 1), (35759, 1), (881983, 1), (173340728312093, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963291 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_10957, prime_oneHundredFiftyTwoET_35759, prime_oneHundredFiftyTwoET_881983, prime_oneHundredFiftyTwoET_173340728312093]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963292 : Nat.totient 179704566383629008981726963292 = 89851724692617996255303128448 := by
  rw [← show ((([(2, 2), (160883, 1), (19481132537, 1), (14334243066613, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963292 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_160883, prime_oneHundredFiftyTwoET_19481132537, prime_oneHundredFiftyTwoET_14334243066613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963293 : Nat.totient 179704566383629008981726963293 = 148763082818825576053443735552 := by
  rw [← show ((([(7, 1), (43, 1), (149, 1), (233, 1), (4339, 1), (80473, 1), (49250493410207, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963293 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_43, prime_oneHundredFiftyTwoET_149, prime_oneHundredFiftyTwoET_233, prime_oneHundredFiftyTwoET_4339, prime_oneHundredFiftyTwoET_80473, prime_oneHundredFiftyTwoET_49250493410207]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963294 : Nat.totient 179704566383629008981726963294 = 59898087248483605364686460160 := by
  rw [← show ((([(2, 1), (3, 1), (17443, 1), (79883233, 1), (21494683197158071, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963294 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_17443, prime_oneHundredFiftyTwoET_79883233, prime_oneHundredFiftyTwoET_21494683197158071]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963295 : Nat.totient 179704566383629008981726963295 = 135583042784321031263636152320 := by
  rw [← show ((([(5, 1), (19, 1), (271, 1), (1217, 1), (4440187, 1), (1291737826932829, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963295 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_19, prime_oneHundredFiftyTwoET_271, prime_oneHundredFiftyTwoET_1217, prime_oneHundredFiftyTwoET_4440187, prime_oneHundredFiftyTwoET_1291737826932829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963296 : Nat.totient 179704566383629008981726963296 = 85943026056057527993604591744 := by
  rw [← show ((([(2, 5), (23, 1), (32603, 1), (7488998344362023941087, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963296 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_23, prime_oneHundredFiftyTwoET_32603, prime_oneHundredFiftyTwoET_7488998344362023941087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963297 : Nat.totient 179704566383629008981726963297 = 119781862561959814008833526720 := by
  rw [← show ((([(3, 2), (6827, 1), (32969, 1), (88711704958154895091, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963297 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_6827, prime_oneHundredFiftyTwoET_32969, prime_oneHundredFiftyTwoET_88711704958154895091]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963298 : Nat.totient 179704566383629008981726963298 = 80491886412013449980330388480 := by
  rw [← show ((([(2, 1), (11, 1), (73, 1), (1103, 1), (9694877, 1), (10463952414478393, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963298 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_11, prime_oneHundredFiftyTwoET_73, prime_oneHundredFiftyTwoET_1103, prime_oneHundredFiftyTwoET_9694877, prime_oneHundredFiftyTwoET_10463952414478393]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963299 : Nat.totient 179704566383629008981726963299 = 179704347815335919071859114400 := by
  rw [← show ((([(885589, 1), (11484661, 1), (17668867706683931, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963299 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_885589, prime_oneHundredFiftyTwoET_11484661, prime_oneHundredFiftyTwoET_17668867706683931]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963300 : Nat.totient 179704566383629008981726963300 = 37568186046480613402644480000 := by
  rw [← show ((([(2, 2), (3, 1), (5, 2), (7, 1), (17, 1), (37, 1), (1279, 1), (2251, 1), (47254495754060453, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963300 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_2, prime_oneHundredFiftyTwoET_3, prime_oneHundredFiftyTwoET_5, prime_oneHundredFiftyTwoET_7, prime_oneHundredFiftyTwoET_17, prime_oneHundredFiftyTwoET_37, prime_oneHundredFiftyTwoET_1279, prime_oneHundredFiftyTwoET_2251, prime_oneHundredFiftyTwoET_47254495754060453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredFiftyTwoET_179704566383629008981726963301 : Nat.totient 179704566383629008981726963301 = 165871545648861285200997469440 := by
  rw [← show ((([(13, 2), (22039, 1), (80341, 1), (140084323, 1), (4287002677, 1)] : List FactorBlock).map factorBlockValue).prod) = 179704566383629008981726963301 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredFiftyTwoET_13, prime_oneHundredFiftyTwoET_22039, prime_oneHundredFiftyTwoET_80341, prime_oneHundredFiftyTwoET_140084323, prime_oneHundredFiftyTwoET_4287002677]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredFiftyTwoET : certifiedKill 1 179704566383629008981726963199 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredFiftyTwoET_179704566383629008981726963200, phi_oneHundredFiftyTwoET_179704566383629008981726963201, phi_oneHundredFiftyTwoET_179704566383629008981726963202,
    phi_oneHundredFiftyTwoET_179704566383629008981726963203, phi_oneHundredFiftyTwoET_179704566383629008981726963204, phi_oneHundredFiftyTwoET_179704566383629008981726963205,
    phi_oneHundredFiftyTwoET_179704566383629008981726963206, phi_oneHundredFiftyTwoET_179704566383629008981726963207, phi_oneHundredFiftyTwoET_179704566383629008981726963208,
    phi_oneHundredFiftyTwoET_179704566383629008981726963209, phi_oneHundredFiftyTwoET_179704566383629008981726963210, phi_oneHundredFiftyTwoET_179704566383629008981726963211,
    phi_oneHundredFiftyTwoET_179704566383629008981726963212, phi_oneHundredFiftyTwoET_179704566383629008981726963213, phi_oneHundredFiftyTwoET_179704566383629008981726963214,
    phi_oneHundredFiftyTwoET_179704566383629008981726963215, phi_oneHundredFiftyTwoET_179704566383629008981726963216, phi_oneHundredFiftyTwoET_179704566383629008981726963217,
    phi_oneHundredFiftyTwoET_179704566383629008981726963218, phi_oneHundredFiftyTwoET_179704566383629008981726963219, phi_oneHundredFiftyTwoET_179704566383629008981726963220,
    phi_oneHundredFiftyTwoET_179704566383629008981726963221, phi_oneHundredFiftyTwoET_179704566383629008981726963222, phi_oneHundredFiftyTwoET_179704566383629008981726963223,
    phi_oneHundredFiftyTwoET_179704566383629008981726963224, phi_oneHundredFiftyTwoET_179704566383629008981726963225, phi_oneHundredFiftyTwoET_179704566383629008981726963226,
    phi_oneHundredFiftyTwoET_179704566383629008981726963227, phi_oneHundredFiftyTwoET_179704566383629008981726963228, phi_oneHundredFiftyTwoET_179704566383629008981726963229,
    phi_oneHundredFiftyTwoET_179704566383629008981726963230, phi_oneHundredFiftyTwoET_179704566383629008981726963231, phi_oneHundredFiftyTwoET_179704566383629008981726963232,
    phi_oneHundredFiftyTwoET_179704566383629008981726963233, phi_oneHundredFiftyTwoET_179704566383629008981726963234, phi_oneHundredFiftyTwoET_179704566383629008981726963235,
    phi_oneHundredFiftyTwoET_179704566383629008981726963236, phi_oneHundredFiftyTwoET_179704566383629008981726963237, phi_oneHundredFiftyTwoET_179704566383629008981726963238,
    phi_oneHundredFiftyTwoET_179704566383629008981726963239, phi_oneHundredFiftyTwoET_179704566383629008981726963240, phi_oneHundredFiftyTwoET_179704566383629008981726963241,
    phi_oneHundredFiftyTwoET_179704566383629008981726963242, phi_oneHundredFiftyTwoET_179704566383629008981726963243, phi_oneHundredFiftyTwoET_179704566383629008981726963244,
    phi_oneHundredFiftyTwoET_179704566383629008981726963245, phi_oneHundredFiftyTwoET_179704566383629008981726963246, phi_oneHundredFiftyTwoET_179704566383629008981726963247,
    phi_oneHundredFiftyTwoET_179704566383629008981726963248, phi_oneHundredFiftyTwoET_179704566383629008981726963249, phi_oneHundredFiftyTwoET_179704566383629008981726963250,
    phi_oneHundredFiftyTwoET_179704566383629008981726963251, phi_oneHundredFiftyTwoET_179704566383629008981726963252, phi_oneHundredFiftyTwoET_179704566383629008981726963253,
    phi_oneHundredFiftyTwoET_179704566383629008981726963254, phi_oneHundredFiftyTwoET_179704566383629008981726963255, phi_oneHundredFiftyTwoET_179704566383629008981726963256,
    phi_oneHundredFiftyTwoET_179704566383629008981726963257, phi_oneHundredFiftyTwoET_179704566383629008981726963258, phi_oneHundredFiftyTwoET_179704566383629008981726963259,
    phi_oneHundredFiftyTwoET_179704566383629008981726963260, phi_oneHundredFiftyTwoET_179704566383629008981726963261, phi_oneHundredFiftyTwoET_179704566383629008981726963262,
    phi_oneHundredFiftyTwoET_179704566383629008981726963263, phi_oneHundredFiftyTwoET_179704566383629008981726963264, phi_oneHundredFiftyTwoET_179704566383629008981726963265,
    phi_oneHundredFiftyTwoET_179704566383629008981726963266, phi_oneHundredFiftyTwoET_179704566383629008981726963267, phi_oneHundredFiftyTwoET_179704566383629008981726963268,
    phi_oneHundredFiftyTwoET_179704566383629008981726963269, phi_oneHundredFiftyTwoET_179704566383629008981726963270, phi_oneHundredFiftyTwoET_179704566383629008981726963271,
    phi_oneHundredFiftyTwoET_179704566383629008981726963272, phi_oneHundredFiftyTwoET_179704566383629008981726963273, phi_oneHundredFiftyTwoET_179704566383629008981726963274,
    phi_oneHundredFiftyTwoET_179704566383629008981726963275, phi_oneHundredFiftyTwoET_179704566383629008981726963276, phi_oneHundredFiftyTwoET_179704566383629008981726963277,
    phi_oneHundredFiftyTwoET_179704566383629008981726963278, phi_oneHundredFiftyTwoET_179704566383629008981726963279, phi_oneHundredFiftyTwoET_179704566383629008981726963280,
    phi_oneHundredFiftyTwoET_179704566383629008981726963281, phi_oneHundredFiftyTwoET_179704566383629008981726963282, phi_oneHundredFiftyTwoET_179704566383629008981726963283,
    phi_oneHundredFiftyTwoET_179704566383629008981726963284, phi_oneHundredFiftyTwoET_179704566383629008981726963285, phi_oneHundredFiftyTwoET_179704566383629008981726963286,
    phi_oneHundredFiftyTwoET_179704566383629008981726963287, phi_oneHundredFiftyTwoET_179704566383629008981726963288, phi_oneHundredFiftyTwoET_179704566383629008981726963289,
    phi_oneHundredFiftyTwoET_179704566383629008981726963290, phi_oneHundredFiftyTwoET_179704566383629008981726963291, phi_oneHundredFiftyTwoET_179704566383629008981726963292,
    phi_oneHundredFiftyTwoET_179704566383629008981726963293, phi_oneHundredFiftyTwoET_179704566383629008981726963294, phi_oneHundredFiftyTwoET_179704566383629008981726963295,
    phi_oneHundredFiftyTwoET_179704566383629008981726963296, phi_oneHundredFiftyTwoET_179704566383629008981726963297, phi_oneHundredFiftyTwoET_179704566383629008981726963298,
    phi_oneHundredFiftyTwoET_179704566383629008981726963299, phi_oneHundredFiftyTwoET_179704566383629008981726963300, phi_oneHundredFiftyTwoET_179704566383629008981726963301]

end TotientTailPeriodKiller
end Erdos249257
