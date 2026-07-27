import Erdos249257.DiagonalPincerCertificatesT64

/- Kernel-checked off-diagonal certificate at a freely chosen position. -/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

private def oneHundredTwentySixDTFastPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  Nat.binaryRec 1 (fun b _ r => if b then r * r * a else r * r) n

private theorem oneHundredTwentySixDTFastPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) : oneHundredTwentySixDTFastPow a n = a ^ n := by
  induction n using Nat.binaryRec with
  | zero => simp [oneHundredTwentySixDTFastPow, Nat.binaryRec_zero]
  | bit b n ih =>
      rw [oneHundredTwentySixDTFastPow, Nat.binaryRec_eq b n (by left; simp)]
      change (if b then oneHundredTwentySixDTFastPow a n * oneHundredTwentySixDTFastPow a n * a else oneHundredTwentySixDTFastPow a n * oneHundredTwentySixDTFastPow a n) = _
      rw [ih]
      cases b <;> simp [Nat.bit, two_mul, pow_add]

private theorem prime_oneHundredTwentySixDT_2 : Nat.Prime 2 := by norm_num

private theorem prime_oneHundredTwentySixDT_3 : Nat.Prime 3 := by norm_num

private theorem prime_oneHundredTwentySixDT_5 : Nat.Prime 5 := by norm_num

private theorem prime_oneHundredTwentySixDT_7 : Nat.Prime 7 := by norm_num

private theorem prime_oneHundredTwentySixDT_11 : Nat.Prime 11 := by norm_num

private theorem prime_oneHundredTwentySixDT_13 : Nat.Prime 13 := by norm_num

private theorem prime_oneHundredTwentySixDT_17 : Nat.Prime 17 := by norm_num

private theorem prime_oneHundredTwentySixDT_19 : Nat.Prime 19 := by norm_num

private theorem prime_oneHundredTwentySixDT_23 : Nat.Prime 23 := by norm_num

private theorem prime_oneHundredTwentySixDT_29 : Nat.Prime 29 := by norm_num

private theorem prime_oneHundredTwentySixDT_31 : Nat.Prime 31 := by norm_num

private theorem prime_oneHundredTwentySixDT_37 : Nat.Prime 37 := by norm_num

private theorem prime_oneHundredTwentySixDT_41 : Nat.Prime 41 := by norm_num

private theorem prime_oneHundredTwentySixDT_43 : Nat.Prime 43 := by norm_num

private theorem prime_oneHundredTwentySixDT_47 : Nat.Prime 47 := by norm_num

private theorem prime_oneHundredTwentySixDT_53 : Nat.Prime 53 := by norm_num

private theorem prime_oneHundredTwentySixDT_59 : Nat.Prime 59 := by norm_num

private theorem prime_oneHundredTwentySixDT_61 : Nat.Prime 61 := by norm_num

private theorem prime_oneHundredTwentySixDT_67 : Nat.Prime 67 := by norm_num

private theorem prime_oneHundredTwentySixDT_71 : Nat.Prime 71 := by norm_num

private theorem prime_oneHundredTwentySixDT_73 : Nat.Prime 73 := by norm_num

private theorem prime_oneHundredTwentySixDT_79 : Nat.Prime 79 := by norm_num

private theorem prime_oneHundredTwentySixDT_83 : Nat.Prime 83 := by norm_num

private theorem prime_oneHundredTwentySixDT_89 : Nat.Prime 89 := by norm_num

private theorem prime_oneHundredTwentySixDT_97 : Nat.Prime 97 := by norm_num

private theorem prime_oneHundredTwentySixDT_101 : Nat.Prime 101 := by norm_num

private theorem prime_oneHundredTwentySixDT_103 : Nat.Prime 103 := by norm_num

private theorem prime_oneHundredTwentySixDT_107 : Nat.Prime 107 := by norm_num

private theorem prime_oneHundredTwentySixDT_109 : Nat.Prime 109 := by norm_num

private theorem prime_oneHundredTwentySixDT_113 : Nat.Prime 113 := by norm_num

private theorem prime_oneHundredTwentySixDT_127 : Nat.Prime 127 := by norm_num

private theorem prime_oneHundredTwentySixDT_131 : Nat.Prime 131 := by norm_num

private theorem prime_oneHundredTwentySixDT_137 : Nat.Prime 137 := by norm_num

private theorem prime_oneHundredTwentySixDT_139 : Nat.Prime 139 := by norm_num

private theorem prime_oneHundredTwentySixDT_149 : Nat.Prime 149 := by norm_num

private theorem prime_oneHundredTwentySixDT_151 : Nat.Prime 151 := by norm_num

private theorem prime_oneHundredTwentySixDT_157 : Nat.Prime 157 := by norm_num

private theorem prime_oneHundredTwentySixDT_163 : Nat.Prime 163 := by norm_num

private theorem prime_oneHundredTwentySixDT_167 : Nat.Prime 167 := by norm_num

private theorem prime_oneHundredTwentySixDT_173 : Nat.Prime 173 := by norm_num

private theorem prime_oneHundredTwentySixDT_179 : Nat.Prime 179 := by norm_num

private theorem prime_oneHundredTwentySixDT_181 : Nat.Prime 181 := by norm_num

private theorem prime_oneHundredTwentySixDT_191 : Nat.Prime 191 := by norm_num

private theorem prime_oneHundredTwentySixDT_193 : Nat.Prime 193 := by norm_num

private theorem prime_oneHundredTwentySixDT_197 : Nat.Prime 197 := by norm_num

private theorem prime_oneHundredTwentySixDT_199 : Nat.Prime 199 := by norm_num

private theorem prime_oneHundredTwentySixDT_211 : Nat.Prime 211 := by norm_num

private theorem prime_oneHundredTwentySixDT_223 : Nat.Prime 223 := by norm_num

private theorem prime_oneHundredTwentySixDT_227 : Nat.Prime 227 := by norm_num

private theorem prime_oneHundredTwentySixDT_229 : Nat.Prime 229 := by norm_num

private theorem prime_oneHundredTwentySixDT_233 : Nat.Prime 233 := by norm_num

private theorem prime_oneHundredTwentySixDT_239 : Nat.Prime 239 := by norm_num

private theorem prime_oneHundredTwentySixDT_241 : Nat.Prime 241 := by norm_num

private theorem prime_oneHundredTwentySixDT_251 : Nat.Prime 251 := by norm_num

private theorem prime_oneHundredTwentySixDT_263 : Nat.Prime 263 := by norm_num

private theorem prime_oneHundredTwentySixDT_269 : Nat.Prime 269 := by norm_num

private theorem prime_oneHundredTwentySixDT_271 : Nat.Prime 271 := by norm_num

private theorem prime_oneHundredTwentySixDT_277 : Nat.Prime 277 := by norm_num

private theorem prime_oneHundredTwentySixDT_283 : Nat.Prime 283 := by norm_num

private theorem prime_oneHundredTwentySixDT_293 : Nat.Prime 293 := by norm_num

private theorem prime_oneHundredTwentySixDT_311 : Nat.Prime 311 := by norm_num

private theorem prime_oneHundredTwentySixDT_313 : Nat.Prime 313 := by norm_num

private theorem prime_oneHundredTwentySixDT_317 : Nat.Prime 317 := by norm_num

private theorem prime_oneHundredTwentySixDT_347 : Nat.Prime 347 := by norm_num

private theorem prime_oneHundredTwentySixDT_353 : Nat.Prime 353 := by norm_num

private theorem prime_oneHundredTwentySixDT_359 : Nat.Prime 359 := by norm_num

private theorem prime_oneHundredTwentySixDT_367 : Nat.Prime 367 := by norm_num

private theorem prime_oneHundredTwentySixDT_373 : Nat.Prime 373 := by norm_num

private theorem prime_oneHundredTwentySixDT_379 : Nat.Prime 379 := by norm_num

private theorem prime_oneHundredTwentySixDT_397 : Nat.Prime 397 := by norm_num

private theorem prime_oneHundredTwentySixDT_401 : Nat.Prime 401 := by norm_num

private theorem prime_oneHundredTwentySixDT_421 : Nat.Prime 421 := by norm_num

private theorem prime_oneHundredTwentySixDT_431 : Nat.Prime 431 := by norm_num

private theorem prime_oneHundredTwentySixDT_433 : Nat.Prime 433 := by norm_num

private theorem prime_oneHundredTwentySixDT_439 : Nat.Prime 439 := by norm_num

private theorem prime_oneHundredTwentySixDT_443 : Nat.Prime 443 := by norm_num

private theorem prime_oneHundredTwentySixDT_449 : Nat.Prime 449 := by norm_num

private theorem prime_oneHundredTwentySixDT_457 : Nat.Prime 457 := by norm_num

private theorem prime_oneHundredTwentySixDT_461 : Nat.Prime 461 := by norm_num

private theorem prime_oneHundredTwentySixDT_463 : Nat.Prime 463 := by norm_num

private theorem prime_oneHundredTwentySixDT_499 : Nat.Prime 499 := by norm_num

private theorem prime_oneHundredTwentySixDT_503 : Nat.Prime 503 := by norm_num

private theorem prime_oneHundredTwentySixDT_557 : Nat.Prime 557 := by norm_num

private theorem prime_oneHundredTwentySixDT_569 : Nat.Prime 569 := by norm_num

private theorem prime_oneHundredTwentySixDT_577 : Nat.Prime 577 := by norm_num

private theorem prime_oneHundredTwentySixDT_587 : Nat.Prime 587 := by norm_num

private theorem prime_oneHundredTwentySixDT_593 : Nat.Prime 593 := by norm_num

private theorem prime_oneHundredTwentySixDT_617 : Nat.Prime 617 := by norm_num

private theorem prime_oneHundredTwentySixDT_631 : Nat.Prime 631 := by norm_num

private theorem prime_oneHundredTwentySixDT_643 : Nat.Prime 643 := by norm_num

private theorem prime_oneHundredTwentySixDT_673 : Nat.Prime 673 := by norm_num

private theorem prime_oneHundredTwentySixDT_677 : Nat.Prime 677 := by norm_num

private theorem prime_oneHundredTwentySixDT_691 : Nat.Prime 691 := by norm_num

private theorem prime_oneHundredTwentySixDT_701 : Nat.Prime 701 := by norm_num

private theorem prime_oneHundredTwentySixDT_709 : Nat.Prime 709 := by norm_num

private theorem prime_oneHundredTwentySixDT_719 : Nat.Prime 719 := by norm_num

private theorem prime_oneHundredTwentySixDT_743 : Nat.Prime 743 := by norm_num

private theorem prime_oneHundredTwentySixDT_797 : Nat.Prime 797 := by norm_num

private theorem prime_oneHundredTwentySixDT_811 : Nat.Prime 811 := by norm_num

private theorem prime_oneHundredTwentySixDT_821 : Nat.Prime 821 := by norm_num

private theorem prime_oneHundredTwentySixDT_827 : Nat.Prime 827 := by norm_num

private theorem prime_oneHundredTwentySixDT_829 : Nat.Prime 829 := by norm_num

private theorem prime_oneHundredTwentySixDT_859 : Nat.Prime 859 := by norm_num

private theorem prime_oneHundredTwentySixDT_863 : Nat.Prime 863 := by norm_num

private theorem prime_oneHundredTwentySixDT_881 : Nat.Prime 881 := by norm_num

private theorem prime_oneHundredTwentySixDT_883 : Nat.Prime 883 := by norm_num

private theorem prime_oneHundredTwentySixDT_929 : Nat.Prime 929 := by norm_num

private theorem prime_oneHundredTwentySixDT_971 : Nat.Prime 971 := by norm_num

private theorem prime_oneHundredTwentySixDT_991 : Nat.Prime 991 := by norm_num

private theorem prime_oneHundredTwentySixDT_1013 : Nat.Prime 1013 := by norm_num

private theorem prime_oneHundredTwentySixDT_1051 : Nat.Prime 1051 := by norm_num

private theorem prime_oneHundredTwentySixDT_1087 : Nat.Prime 1087 := by norm_num

private theorem prime_oneHundredTwentySixDT_1103 : Nat.Prime 1103 := by norm_num

private theorem prime_oneHundredTwentySixDT_1109 : Nat.Prime 1109 := by norm_num

private theorem prime_oneHundredTwentySixDT_1153 : Nat.Prime 1153 := by norm_num

private theorem prime_oneHundredTwentySixDT_1171 : Nat.Prime 1171 := by norm_num

private theorem prime_oneHundredTwentySixDT_1181 : Nat.Prime 1181 := by norm_num

private theorem prime_oneHundredTwentySixDT_1217 : Nat.Prime 1217 := by norm_num

private theorem prime_oneHundredTwentySixDT_1229 : Nat.Prime 1229 := by norm_num

private theorem prime_oneHundredTwentySixDT_1231 : Nat.Prime 1231 := by norm_num

private theorem prime_oneHundredTwentySixDT_1283 : Nat.Prime 1283 := by norm_num

private theorem prime_oneHundredTwentySixDT_1321 : Nat.Prime 1321 := by norm_num

private theorem prime_oneHundredTwentySixDT_1429 : Nat.Prime 1429 := by norm_num

private theorem prime_oneHundredTwentySixDT_1451 : Nat.Prime 1451 := by norm_num

private theorem prime_oneHundredTwentySixDT_1489 : Nat.Prime 1489 := by norm_num

private theorem prime_oneHundredTwentySixDT_1511 : Nat.Prime 1511 := by norm_num

private theorem prime_oneHundredTwentySixDT_1523 : Nat.Prime 1523 := by norm_num

private theorem prime_oneHundredTwentySixDT_1531 : Nat.Prime 1531 := by norm_num

private theorem prime_oneHundredTwentySixDT_1549 : Nat.Prime 1549 := by norm_num

private theorem prime_oneHundredTwentySixDT_1559 : Nat.Prime 1559 := by norm_num

private theorem prime_oneHundredTwentySixDT_1567 : Nat.Prime 1567 := by norm_num

private theorem prime_oneHundredTwentySixDT_1583 : Nat.Prime 1583 := by norm_num

private theorem prime_oneHundredTwentySixDT_1667 : Nat.Prime 1667 := by norm_num

private theorem prime_oneHundredTwentySixDT_1709 : Nat.Prime 1709 := by norm_num

private theorem prime_oneHundredTwentySixDT_1721 : Nat.Prime 1721 := by norm_num

private theorem prime_oneHundredTwentySixDT_1777 : Nat.Prime 1777 := by norm_num

private theorem prime_oneHundredTwentySixDT_1787 : Nat.Prime 1787 := by norm_num

private theorem prime_oneHundredTwentySixDT_1811 : Nat.Prime 1811 := by norm_num

private theorem prime_oneHundredTwentySixDT_1861 : Nat.Prime 1861 := by norm_num

private theorem prime_oneHundredTwentySixDT_1871 : Nat.Prime 1871 := by norm_num

private theorem prime_oneHundredTwentySixDT_2029 : Nat.Prime 2029 := by norm_num

private theorem prime_oneHundredTwentySixDT_2081 : Nat.Prime 2081 := by norm_num

private theorem prime_oneHundredTwentySixDT_2113 : Nat.Prime 2113 := by norm_num

private theorem prime_oneHundredTwentySixDT_2131 : Nat.Prime 2131 := by norm_num

private theorem prime_oneHundredTwentySixDT_2267 : Nat.Prime 2267 := by norm_num

private theorem prime_oneHundredTwentySixDT_2269 : Nat.Prime 2269 := by norm_num

private theorem prime_oneHundredTwentySixDT_2311 : Nat.Prime 2311 := by norm_num

private theorem prime_oneHundredTwentySixDT_2333 : Nat.Prime 2333 := by norm_num

private theorem prime_oneHundredTwentySixDT_2339 : Nat.Prime 2339 := by norm_num

private theorem prime_oneHundredTwentySixDT_2411 : Nat.Prime 2411 := by norm_num

private theorem prime_oneHundredTwentySixDT_2543 : Nat.Prime 2543 := by norm_num

private theorem prime_oneHundredTwentySixDT_2551 : Nat.Prime 2551 := by norm_num

private theorem prime_oneHundredTwentySixDT_2557 : Nat.Prime 2557 := by norm_num

private theorem prime_oneHundredTwentySixDT_2579 : Nat.Prime 2579 := by norm_num

private theorem prime_oneHundredTwentySixDT_2659 : Nat.Prime 2659 := by norm_num

private theorem prime_oneHundredTwentySixDT_2843 : Nat.Prime 2843 := by norm_num

private theorem prime_oneHundredTwentySixDT_2903 : Nat.Prime 2903 := by norm_num

private theorem prime_oneHundredTwentySixDT_3163 : Nat.Prime 3163 := by norm_num

private theorem prime_oneHundredTwentySixDT_3169 : Nat.Prime 3169 := by norm_num

private theorem prime_oneHundredTwentySixDT_3203 : Nat.Prime 3203 := by norm_num

private theorem prime_oneHundredTwentySixDT_3217 : Nat.Prime 3217 := by norm_num

private theorem prime_oneHundredTwentySixDT_3389 : Nat.Prime 3389 := by norm_num

private theorem prime_oneHundredTwentySixDT_3499 : Nat.Prime 3499 := by norm_num

private theorem prime_oneHundredTwentySixDT_3541 : Nat.Prime 3541 := by norm_num

private theorem prime_oneHundredTwentySixDT_3637 : Nat.Prime 3637 := by norm_num

private theorem prime_oneHundredTwentySixDT_3673 : Nat.Prime 3673 := by norm_num

private theorem prime_oneHundredTwentySixDT_3733 : Nat.Prime 3733 := by norm_num

private theorem prime_oneHundredTwentySixDT_3793 : Nat.Prime 3793 := by norm_num

private theorem prime_oneHundredTwentySixDT_3931 : Nat.Prime 3931 := by norm_num

private theorem prime_oneHundredTwentySixDT_4013 : Nat.Prime 4013 := by norm_num

private theorem prime_oneHundredTwentySixDT_4339 : Nat.Prime 4339 := by norm_num

private theorem prime_oneHundredTwentySixDT_4523 : Nat.Prime 4523 := by norm_num

private theorem prime_oneHundredTwentySixDT_4703 : Nat.Prime 4703 := by norm_num

private theorem prime_oneHundredTwentySixDT_4723 : Nat.Prime 4723 := by norm_num

private theorem prime_oneHundredTwentySixDT_4733 : Nat.Prime 4733 := by norm_num

private theorem prime_oneHundredTwentySixDT_4871 : Nat.Prime 4871 := by norm_num

private theorem prime_oneHundredTwentySixDT_4937 : Nat.Prime 4937 := by norm_num

private theorem prime_oneHundredTwentySixDT_5003 : Nat.Prime 5003 := by norm_num

private theorem prime_oneHundredTwentySixDT_5059 : Nat.Prime 5059 := by norm_num

private theorem prime_oneHundredTwentySixDT_5147 : Nat.Prime 5147 := by norm_num

private theorem prime_oneHundredTwentySixDT_5153 : Nat.Prime 5153 := by norm_num

private theorem prime_oneHundredTwentySixDT_5189 : Nat.Prime 5189 := by norm_num

private theorem prime_oneHundredTwentySixDT_5333 : Nat.Prime 5333 := by norm_num

private theorem prime_oneHundredTwentySixDT_5651 : Nat.Prime 5651 := by norm_num

private theorem prime_oneHundredTwentySixDT_5711 : Nat.Prime 5711 := by norm_num

private theorem prime_oneHundredTwentySixDT_6011 : Nat.Prime 6011 := by norm_num

private theorem prime_oneHundredTwentySixDT_6271 : Nat.Prime 6271 := by norm_num

private theorem prime_oneHundredTwentySixDT_6323 : Nat.Prime 6323 := by norm_num

private theorem prime_oneHundredTwentySixDT_6367 : Nat.Prime 6367 := by norm_num

private theorem prime_oneHundredTwentySixDT_6427 : Nat.Prime 6427 := by norm_num

private theorem prime_oneHundredTwentySixDT_6703 : Nat.Prime 6703 := by norm_num

private theorem prime_oneHundredTwentySixDT_6803 : Nat.Prime 6803 := by norm_num

private theorem prime_oneHundredTwentySixDT_6833 : Nat.Prime 6833 := by norm_num

private theorem prime_oneHundredTwentySixDT_6863 : Nat.Prime 6863 := by norm_num

private theorem prime_oneHundredTwentySixDT_6871 : Nat.Prime 6871 := by norm_num

private theorem prime_oneHundredTwentySixDT_7027 : Nat.Prime 7027 := by norm_num

private theorem prime_oneHundredTwentySixDT_7039 : Nat.Prime 7039 := by norm_num

private theorem prime_oneHundredTwentySixDT_7477 : Nat.Prime 7477 := by norm_num

private theorem prime_oneHundredTwentySixDT_7573 : Nat.Prime 7573 := by norm_num

private theorem prime_oneHundredTwentySixDT_7789 : Nat.Prime 7789 := by norm_num

private theorem prime_oneHundredTwentySixDT_7793 : Nat.Prime 7793 := by norm_num

private theorem prime_oneHundredTwentySixDT_8093 : Nat.Prime 8093 := by norm_num

private theorem prime_oneHundredTwentySixDT_8273 : Nat.Prime 8273 := by norm_num

private theorem prime_oneHundredTwentySixDT_8423 : Nat.Prime 8423 := by norm_num

private theorem prime_oneHundredTwentySixDT_8647 : Nat.Prime 8647 := by norm_num

private theorem prime_oneHundredTwentySixDT_8689 : Nat.Prime 8689 := by norm_num

private theorem prime_oneHundredTwentySixDT_8753 : Nat.Prime 8753 := by norm_num

private theorem prime_oneHundredTwentySixDT_9157 : Nat.Prime 9157 := by norm_num

private theorem prime_oneHundredTwentySixDT_9419 : Nat.Prime 9419 := by norm_num

private theorem prime_oneHundredTwentySixDT_9479 : Nat.Prime 9479 := by norm_num

private theorem prime_oneHundredTwentySixDT_9769 : Nat.Prime 9769 := by norm_num

private theorem prime_oneHundredTwentySixDT_10037 : Nat.Prime 10037 := by norm_num

private theorem prime_oneHundredTwentySixDT_10061 : Nat.Prime 10061 := by norm_num

private theorem prime_oneHundredTwentySixDT_10303 : Nat.Prime 10303 := by norm_num

private theorem prime_oneHundredTwentySixDT_10781 : Nat.Prime 10781 := by norm_num

private theorem prime_oneHundredTwentySixDT_10837 : Nat.Prime 10837 := by norm_num

private theorem prime_oneHundredTwentySixDT_10883 : Nat.Prime 10883 := by norm_num

private theorem prime_oneHundredTwentySixDT_11789 : Nat.Prime 11789 := by norm_num

private theorem prime_oneHundredTwentySixDT_12343 : Nat.Prime 12343 := by norm_num

private theorem prime_oneHundredTwentySixDT_12553 : Nat.Prime 12553 := by norm_num

private theorem prime_oneHundredTwentySixDT_12781 : Nat.Prime 12781 := by norm_num

private theorem prime_oneHundredTwentySixDT_12823 : Nat.Prime 12823 := by norm_num

private theorem prime_oneHundredTwentySixDT_12941 : Nat.Prime 12941 := by norm_num

private theorem prime_oneHundredTwentySixDT_13397 : Nat.Prime 13397 := by norm_num

private theorem prime_oneHundredTwentySixDT_13681 : Nat.Prime 13681 := by norm_num

private theorem prime_oneHundredTwentySixDT_14033 : Nat.Prime 14033 := by norm_num

private theorem prime_oneHundredTwentySixDT_14543 : Nat.Prime 14543 := by norm_num

private theorem prime_oneHundredTwentySixDT_14627 : Nat.Prime 14627 := by norm_num

private theorem prime_oneHundredTwentySixDT_14737 : Nat.Prime 14737 := by norm_num

private theorem prime_oneHundredTwentySixDT_15137 : Nat.Prime 15137 := by norm_num

private theorem prime_oneHundredTwentySixDT_15661 : Nat.Prime 15661 := by norm_num

private theorem prime_oneHundredTwentySixDT_16139 : Nat.Prime 16139 := by norm_num

private theorem prime_oneHundredTwentySixDT_16339 : Nat.Prime 16339 := by norm_num

private theorem prime_oneHundredTwentySixDT_16787 : Nat.Prime 16787 := by norm_num

private theorem prime_oneHundredTwentySixDT_17203 : Nat.Prime 17203 := by norm_num

private theorem prime_oneHundredTwentySixDT_17207 : Nat.Prime 17207 := by norm_num

private theorem prime_oneHundredTwentySixDT_17509 : Nat.Prime 17509 := by norm_num

private theorem prime_oneHundredTwentySixDT_18583 : Nat.Prime 18583 := by norm_num

private theorem prime_oneHundredTwentySixDT_20599 : Nat.Prime 20599 := by norm_num

private theorem prime_oneHundredTwentySixDT_20753 : Nat.Prime 20753 := by norm_num

private theorem prime_oneHundredTwentySixDT_21247 : Nat.Prime 21247 := by norm_num

private theorem prime_oneHundredTwentySixDT_21617 : Nat.Prime 21617 := by norm_num

private theorem prime_oneHundredTwentySixDT_22051 : Nat.Prime 22051 := by norm_num

private theorem prime_oneHundredTwentySixDT_22283 : Nat.Prime 22283 := by norm_num

private theorem prime_oneHundredTwentySixDT_22699 : Nat.Prime 22699 := by norm_num

private theorem prime_oneHundredTwentySixDT_23929 : Nat.Prime 23929 := by norm_num

private theorem prime_oneHundredTwentySixDT_25117 : Nat.Prime 25117 := by norm_num

private theorem prime_oneHundredTwentySixDT_25169 : Nat.Prime 25169 := by norm_num

private theorem prime_oneHundredTwentySixDT_25303 : Nat.Prime 25303 := by norm_num

private theorem prime_oneHundredTwentySixDT_26083 : Nat.Prime 26083 := by norm_num

private theorem prime_oneHundredTwentySixDT_26171 : Nat.Prime 26171 := by norm_num

private theorem prime_oneHundredTwentySixDT_28403 : Nat.Prime 28403 := by norm_num

private theorem prime_oneHundredTwentySixDT_29023 : Nat.Prime 29023 := by norm_num

private theorem prime_oneHundredTwentySixDT_29347 : Nat.Prime 29347 := by norm_num

private theorem prime_oneHundredTwentySixDT_29437 : Nat.Prime 29437 := by norm_num

private theorem prime_oneHundredTwentySixDT_31039 : Nat.Prime 31039 := by norm_num

private theorem prime_oneHundredTwentySixDT_31177 : Nat.Prime 31177 := by norm_num

private theorem prime_oneHundredTwentySixDT_31333 : Nat.Prime 31333 := by norm_num

private theorem prime_oneHundredTwentySixDT_31547 : Nat.Prime 31547 := by norm_num

private theorem prime_oneHundredTwentySixDT_32497 : Nat.Prime 32497 := by norm_num

private theorem prime_oneHundredTwentySixDT_32987 : Nat.Prime 32987 := by norm_num

private theorem prime_oneHundredTwentySixDT_36097 : Nat.Prime 36097 := by norm_num

private theorem prime_oneHundredTwentySixDT_36629 : Nat.Prime 36629 := by norm_num

private theorem prime_oneHundredTwentySixDT_36637 : Nat.Prime 36637 := by norm_num

private theorem prime_oneHundredTwentySixDT_36901 : Nat.Prime 36901 := by norm_num

private theorem prime_oneHundredTwentySixDT_37643 : Nat.Prime 37643 := by norm_num

private theorem prime_oneHundredTwentySixDT_37897 : Nat.Prime 37897 := by norm_num

private theorem prime_oneHundredTwentySixDT_38167 : Nat.Prime 38167 := by norm_num

private theorem prime_oneHundredTwentySixDT_38459 : Nat.Prime 38459 := by norm_num

private theorem prime_oneHundredTwentySixDT_39239 : Nat.Prime 39239 := by norm_num

private theorem prime_oneHundredTwentySixDT_40973 : Nat.Prime 40973 := by norm_num

private theorem prime_oneHundredTwentySixDT_42337 : Nat.Prime 42337 := by norm_num

private theorem prime_oneHundredTwentySixDT_43117 : Nat.Prime 43117 := by norm_num

private theorem prime_oneHundredTwentySixDT_44701 : Nat.Prime 44701 := by norm_num

private theorem prime_oneHundredTwentySixDT_44797 : Nat.Prime 44797 := by norm_num

private theorem prime_oneHundredTwentySixDT_46381 : Nat.Prime 46381 := by norm_num

private theorem prime_oneHundredTwentySixDT_47713 : Nat.Prime 47713 := by norm_num

private theorem prime_oneHundredTwentySixDT_48017 : Nat.Prime 48017 := by norm_num

private theorem prime_oneHundredTwentySixDT_53791 : Nat.Prime 53791 := by norm_num

private theorem prime_oneHundredTwentySixDT_58943 : Nat.Prime 58943 := by norm_num

private theorem prime_oneHundredTwentySixDT_62873 : Nat.Prime 62873 := by norm_num

private theorem prime_oneHundredTwentySixDT_63347 : Nat.Prime 63347 := by norm_num

private theorem prime_oneHundredTwentySixDT_65033 : Nat.Prime 65033 := by norm_num

private theorem prime_oneHundredTwentySixDT_65629 : Nat.Prime 65629 := by norm_num

private theorem prime_oneHundredTwentySixDT_66373 : Nat.Prime 66373 := by norm_num

private theorem prime_oneHundredTwentySixDT_66943 : Nat.Prime 66943 := by norm_num

private theorem prime_oneHundredTwentySixDT_69143 : Nat.Prime 69143 := by norm_num

private theorem prime_oneHundredTwentySixDT_69877 : Nat.Prime 69877 := by norm_num

private theorem prime_oneHundredTwentySixDT_69997 : Nat.Prime 69997 := by norm_num

private theorem prime_oneHundredTwentySixDT_75253 : Nat.Prime 75253 := by norm_num

private theorem prime_oneHundredTwentySixDT_76163 : Nat.Prime 76163 := by norm_num

private theorem prime_oneHundredTwentySixDT_76481 : Nat.Prime 76481 := by norm_num

private theorem prime_oneHundredTwentySixDT_79847 : Nat.Prime 79847 := by norm_num

private theorem prime_oneHundredTwentySixDT_80039 : Nat.Prime 80039 := by norm_num

private theorem prime_oneHundredTwentySixDT_80603 : Nat.Prime 80603 := by norm_num

private theorem prime_oneHundredTwentySixDT_81119 : Nat.Prime 81119 := by norm_num

private theorem prime_oneHundredTwentySixDT_82223 : Nat.Prime 82223 := by norm_num

private theorem prime_oneHundredTwentySixDT_84389 : Nat.Prime 84389 := by norm_num

private theorem prime_oneHundredTwentySixDT_85621 : Nat.Prime 85621 := by norm_num

private theorem prime_oneHundredTwentySixDT_86579 : Nat.Prime 86579 := by norm_num

private theorem prime_oneHundredTwentySixDT_97157 : Nat.Prime 97157 := by norm_num

private theorem prime_oneHundredTwentySixDT_97453 : Nat.Prime 97453 := by norm_num

private theorem prime_oneHundredTwentySixDT_103981 : Nat.Prime 103981 := by norm_num

private theorem prime_oneHundredTwentySixDT_104161 : Nat.Prime 104161 := by norm_num

private theorem prime_oneHundredTwentySixDT_106621 : Nat.Prime 106621 := by norm_num

private theorem prime_oneHundredTwentySixDT_106861 : Nat.Prime 106861 := by norm_num

private theorem prime_oneHundredTwentySixDT_109849 : Nat.Prime 109849 := by norm_num

private theorem prime_oneHundredTwentySixDT_110933 : Nat.Prime 110933 := by norm_num

private theorem prime_oneHundredTwentySixDT_113357 : Nat.Prime 113357 := by norm_num

private theorem prime_oneHundredTwentySixDT_120671 : Nat.Prime 120671 := by norm_num

private theorem prime_oneHundredTwentySixDT_125287 : Nat.Prime 125287 := by norm_num

private theorem prime_oneHundredTwentySixDT_127163 : Nat.Prime 127163 := by norm_num

private theorem prime_oneHundredTwentySixDT_130411 : Nat.Prime 130411 := by norm_num

private theorem prime_oneHundredTwentySixDT_131627 : Nat.Prime 131627 := by norm_num

private theorem prime_oneHundredTwentySixDT_141937 : Nat.Prime 141937 := by norm_num

private theorem prime_oneHundredTwentySixDT_142799 : Nat.Prime 142799 := by norm_num

private theorem prime_oneHundredTwentySixDT_145829 : Nat.Prime 145829 := by norm_num

private theorem prime_oneHundredTwentySixDT_146213 : Nat.Prime 146213 := by norm_num

private theorem prime_oneHundredTwentySixDT_147503 : Nat.Prime 147503 := by norm_num

private theorem prime_oneHundredTwentySixDT_148193 : Nat.Prime 148193 := by norm_num

private theorem prime_oneHundredTwentySixDT_162971 : Nat.Prime 162971 := by norm_num

private theorem prime_oneHundredTwentySixDT_165437 : Nat.Prime 165437 := by norm_num

private theorem prime_oneHundredTwentySixDT_166147 : Nat.Prime 166147 := by norm_num

private theorem prime_oneHundredTwentySixDT_167033 : Nat.Prime 167033 := by norm_num

private theorem prime_oneHundredTwentySixDT_171401 : Nat.Prime 171401 := by norm_num

private theorem prime_oneHundredTwentySixDT_172049 : Nat.Prime 172049 := by norm_num

private theorem prime_oneHundredTwentySixDT_182239 : Nat.Prime 182239 := by norm_num

private theorem prime_oneHundredTwentySixDT_188911 : Nat.Prime 188911 := by norm_num

private theorem prime_oneHundredTwentySixDT_197773 : Nat.Prime 197773 := by norm_num

private theorem prime_oneHundredTwentySixDT_200789 : Nat.Prime 200789 := by norm_num

private theorem prime_oneHundredTwentySixDT_221069 : Nat.Prime 221069 := by norm_num

private theorem prime_oneHundredTwentySixDT_224291 : Nat.Prime 224291 := by norm_num

private theorem prime_oneHundredTwentySixDT_226813 : Nat.Prime 226813 := by norm_num

private theorem prime_oneHundredTwentySixDT_230149 : Nat.Prime 230149 := by norm_num

private theorem prime_oneHundredTwentySixDT_239333 : Nat.Prime 239333 := by norm_num

private theorem prime_oneHundredTwentySixDT_241603 : Nat.Prime 241603 := by norm_num

private theorem prime_oneHundredTwentySixDT_265709 : Nat.Prime 265709 := by norm_num

private theorem prime_oneHundredTwentySixDT_269851 : Nat.Prime 269851 := by norm_num

private theorem prime_oneHundredTwentySixDT_271163 : Nat.Prime 271163 := by norm_num

private theorem prime_oneHundredTwentySixDT_277577 : Nat.Prime 277577 := by norm_num

private theorem prime_oneHundredTwentySixDT_282713 : Nat.Prime 282713 := by norm_num

private theorem prime_oneHundredTwentySixDT_284833 : Nat.Prime 284833 := by norm_num

private theorem prime_oneHundredTwentySixDT_289103 : Nat.Prime 289103 := by norm_num

private theorem prime_oneHundredTwentySixDT_296941 : Nat.Prime 296941 := by norm_num

private theorem prime_oneHundredTwentySixDT_302663 : Nat.Prime 302663 := by norm_num

private theorem prime_oneHundredTwentySixDT_323093 : Nat.Prime 323093 := by norm_num

private theorem prime_oneHundredTwentySixDT_329863 : Nat.Prime 329863 := by norm_num

private theorem prime_oneHundredTwentySixDT_335077 : Nat.Prime 335077 := by norm_num

private theorem prime_oneHundredTwentySixDT_341461 : Nat.Prime 341461 := by norm_num

private theorem prime_oneHundredTwentySixDT_356333 : Nat.Prime 356333 := by norm_num

private theorem prime_oneHundredTwentySixDT_364979 : Nat.Prime 364979 := by norm_num

private theorem prime_oneHundredTwentySixDT_376003 : Nat.Prime 376003 := by norm_num

private theorem prime_oneHundredTwentySixDT_378137 : Nat.Prime 378137 := by norm_num

private theorem prime_oneHundredTwentySixDT_381631 : Nat.Prime 381631 := by norm_num

private theorem prime_oneHundredTwentySixDT_394717 : Nat.Prime 394717 := by norm_num

private theorem prime_oneHundredTwentySixDT_410411 : Nat.Prime 410411 := by norm_num

private theorem prime_oneHundredTwentySixDT_439583 : Nat.Prime 439583 := by norm_num

private theorem prime_oneHundredTwentySixDT_457757 : Nat.Prime 457757 := by norm_num

private theorem prime_oneHundredTwentySixDT_458747 : Nat.Prime 458747 := by norm_num

private theorem prime_oneHundredTwentySixDT_501827 : Nat.Prime 501827 := by norm_num

private theorem prime_oneHundredTwentySixDT_519119 : Nat.Prime 519119 := by norm_num

private theorem prime_oneHundredTwentySixDT_547999 : Nat.Prime 547999 := by norm_num

private theorem prime_oneHundredTwentySixDT_570881 : Nat.Prime 570881 := by norm_num

private theorem prime_oneHundredTwentySixDT_572777 : Nat.Prime 572777 := by norm_num

private theorem prime_oneHundredTwentySixDT_631867 : Nat.Prime 631867 := by norm_num

private theorem prime_oneHundredTwentySixDT_653339 : Nat.Prime 653339 := by norm_num

private theorem prime_oneHundredTwentySixDT_653647 : Nat.Prime 653647 := by norm_num

private theorem prime_oneHundredTwentySixDT_721333 : Nat.Prime 721333 := by norm_num

private theorem prime_oneHundredTwentySixDT_778979 : Nat.Prime 778979 := by norm_num

private theorem prime_oneHundredTwentySixDT_792613 : Nat.Prime 792613 := by norm_num

private theorem prime_oneHundredTwentySixDT_857453 : Nat.Prime 857453 := by norm_num

private theorem prime_oneHundredTwentySixDT_873113 : Nat.Prime 873113 := by norm_num

private theorem prime_oneHundredTwentySixDT_939391 : Nat.Prime 939391 := by norm_num

private theorem prime_oneHundredTwentySixDT_944261 : Nat.Prime 944261 := by norm_num

private theorem prime_oneHundredTwentySixDT_991741 : Nat.Prime 991741 := by norm_num

private theorem prime_oneHundredTwentySixDT_1020233 : Nat.Prime 1020233 := by norm_num

private theorem prime_oneHundredTwentySixDT_1025839 : Nat.Prime 1025839 := by norm_num

private theorem prime_oneHundredTwentySixDT_1080589 : Nat.Prime 1080589 := by norm_num

private theorem prime_oneHundredTwentySixDT_1095491 : Nat.Prime 1095491 := by norm_num

private theorem prime_oneHundredTwentySixDT_1152937 : Nat.Prime 1152937 := by norm_num

private theorem prime_oneHundredTwentySixDT_1154401 : Nat.Prime 1154401 := by norm_num

private theorem prime_oneHundredTwentySixDT_1182283 : Nat.Prime 1182283 := by norm_num

private theorem prime_oneHundredTwentySixDT_1201601 : Nat.Prime 1201601 := by norm_num

private theorem prime_oneHundredTwentySixDT_1244279 : Nat.Prime 1244279 := by norm_num

private theorem prime_oneHundredTwentySixDT_1245779 : Nat.Prime 1245779 := by norm_num

private theorem prime_oneHundredTwentySixDT_1256729 : Nat.Prime 1256729 := by norm_num

private theorem prime_oneHundredTwentySixDT_1430321 : Nat.Prime 1430321 := by norm_num

private theorem prime_oneHundredTwentySixDT_1442173 : Nat.Prime 1442173 := by norm_num

private theorem prime_oneHundredTwentySixDT_1508081 : Nat.Prime 1508081 := by norm_num

private theorem prime_oneHundredTwentySixDT_1521643 : Nat.Prime 1521643 := by norm_num

private theorem prime_oneHundredTwentySixDT_1562173 : Nat.Prime 1562173 := by norm_num

private theorem prime_oneHundredTwentySixDT_1592737 : Nat.Prime 1592737 := by norm_num

private theorem prime_oneHundredTwentySixDT_1731589 : Nat.Prime 1731589 := by norm_num

private theorem prime_oneHundredTwentySixDT_1743487 : Nat.Prime 1743487 := by norm_num

private theorem prime_oneHundredTwentySixDT_1902517 : Nat.Prime 1902517 := by norm_num

private theorem prime_oneHundredTwentySixDT_2282047 : Nat.Prime 2282047 := by norm_num

private theorem prime_oneHundredTwentySixDT_2489909 : Nat.Prime 2489909 := by norm_num

private theorem prime_oneHundredTwentySixDT_2514527 : Nat.Prime 2514527 := by norm_num

private theorem prime_oneHundredTwentySixDT_2672987 : Nat.Prime 2672987 := by norm_num

private theorem prime_oneHundredTwentySixDT_2681039 : Nat.Prime 2681039 := by norm_num

private theorem prime_oneHundredTwentySixDT_2991629 : Nat.Prime 2991629 := by norm_num

private theorem prime_oneHundredTwentySixDT_3048173 : Nat.Prime 3048173 := by norm_num

private theorem prime_oneHundredTwentySixDT_3086389 : Nat.Prime 3086389 := by norm_num

private theorem prime_oneHundredTwentySixDT_3249863 : Nat.Prime 3249863 := by norm_num

private theorem prime_oneHundredTwentySixDT_3336167 : Nat.Prime 3336167 := by norm_num

private theorem prime_oneHundredTwentySixDT_3935629 : Nat.Prime 3935629 := by norm_num

private theorem prime_oneHundredTwentySixDT_4003579 : Nat.Prime 4003579 := by norm_num

private theorem prime_oneHundredTwentySixDT_4172341 : Nat.Prime 4172341 := by norm_num

private theorem prime_oneHundredTwentySixDT_4282273 : Nat.Prime 4282273 := by norm_num

private theorem prime_oneHundredTwentySixDT_4513123 : Nat.Prime 4513123 := by norm_num

private theorem prime_oneHundredTwentySixDT_4607093 : Nat.Prime 4607093 := by norm_num

private theorem prime_oneHundredTwentySixDT_4615783 : Nat.Prime 4615783 := by norm_num

private theorem prime_oneHundredTwentySixDT_4771391 : Nat.Prime 4771391 := by norm_num

private theorem prime_oneHundredTwentySixDT_4780337 : Nat.Prime 4780337 := by norm_num

private theorem prime_oneHundredTwentySixDT_5002103 : Nat.Prime 5002103 := by norm_num

private theorem prime_oneHundredTwentySixDT_5285387 : Nat.Prime 5285387 := by norm_num

private theorem prime_oneHundredTwentySixDT_5506091 : Nat.Prime 5506091 := by norm_num

private theorem prime_oneHundredTwentySixDT_5731729 : Nat.Prime 5731729 := by norm_num

private theorem prime_oneHundredTwentySixDT_5816549 : Nat.Prime 5816549 := by norm_num

private theorem prime_oneHundredTwentySixDT_6174811 : Nat.Prime 6174811 := by norm_num

private theorem prime_oneHundredTwentySixDT_6227671 : Nat.Prime 6227671 := by norm_num

private theorem prime_oneHundredTwentySixDT_6314617 : Nat.Prime 6314617 := by norm_num

private theorem prime_oneHundredTwentySixDT_6336347 : Nat.Prime 6336347 := by norm_num

private theorem prime_oneHundredTwentySixDT_7290317 : Nat.Prime 7290317 := by norm_num

private theorem prime_oneHundredTwentySixDT_7366897 : Nat.Prime 7366897 := by norm_num

private theorem prime_oneHundredTwentySixDT_7521277 : Nat.Prime 7521277 := by norm_num

private theorem prime_oneHundredTwentySixDT_7998937 : Nat.Prime 7998937 := by norm_num

private theorem prime_oneHundredTwentySixDT_9775933 : Nat.Prime 9775933 := by norm_num

private theorem prime_oneHundredTwentySixDT_10492747 : Nat.Prime 10492747 := by norm_num

private theorem prime_oneHundredTwentySixDT_10820141 : Nat.Prime 10820141 := by norm_num

private theorem prime_oneHundredTwentySixDT_10993193 : Nat.Prime 10993193 := by norm_num

private theorem prime_oneHundredTwentySixDT_11874197 : Nat.Prime 11874197 := by norm_num

private theorem prime_oneHundredTwentySixDT_12041273 : Nat.Prime 12041273 := by norm_num

private theorem prime_oneHundredTwentySixDT_12983963 : Nat.Prime 12983963 := by norm_num

private theorem prime_oneHundredTwentySixDT_13231891 : Nat.Prime 13231891 := by norm_num

private theorem prime_oneHundredTwentySixDT_13940543 : Nat.Prime 13940543 := by norm_num

private theorem prime_oneHundredTwentySixDT_14668343 : Nat.Prime 14668343 := by norm_num

private theorem prime_oneHundredTwentySixDT_15263719 : Nat.Prime 15263719 := by norm_num

private theorem prime_oneHundredTwentySixDT_15277019 : Nat.Prime 15277019 := by norm_num

private theorem prime_oneHundredTwentySixDT_15826513 : Nat.Prime 15826513 := by norm_num

private theorem prime_oneHundredTwentySixDT_16044541 : Nat.Prime 16044541 := by norm_num

private theorem prime_oneHundredTwentySixDT_16727479 : Nat.Prime 16727479 := by norm_num

private theorem prime_oneHundredTwentySixDT_17516843 : Nat.Prime 17516843 := by norm_num

private theorem prime_oneHundredTwentySixDT_18136319 : Nat.Prime 18136319 := by norm_num

private theorem prime_oneHundredTwentySixDT_18262633 : Nat.Prime 18262633 := by norm_num

private theorem prime_oneHundredTwentySixDT_19135813 : Nat.Prime 19135813 := by norm_num

private theorem prime_oneHundredTwentySixDT_21099097 : Nat.Prime 21099097 := by norm_num

private theorem prime_oneHundredTwentySixDT_23630317 : Nat.Prime 23630317 := by norm_num

private theorem prime_oneHundredTwentySixDT_25863419 : Nat.Prime 25863419 := by norm_num

private theorem prime_oneHundredTwentySixDT_26544449 : Nat.Prime 26544449 := by norm_num

private theorem prime_oneHundredTwentySixDT_26859463 : Nat.Prime 26859463 := by norm_num

private theorem prime_oneHundredTwentySixDT_26895587 : Nat.Prime 26895587 := by norm_num

private theorem prime_oneHundredTwentySixDT_27398863 : Nat.Prime 27398863 := by norm_num

private theorem prime_oneHundredTwentySixDT_28246531 : Nat.Prime 28246531 := by norm_num

private theorem prime_oneHundredTwentySixDT_29290621 : Nat.Prime 29290621 := by norm_num

private theorem prime_oneHundredTwentySixDT_30755359 : Nat.Prime 30755359 := by
  apply lucas_primality 30755359 (6 : ZMod 30755359)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (157, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (157, 1), (10883, 1)] : List FactorBlock).map factorBlockValue).prod) = 30755359 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_157
      · exact prime_oneHundredTwentySixDT_10883
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 30755359) ^ 15377679 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 30755359) ^ 10251786 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 30755359) ^ 195894 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 30755359) ^ 2826 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_31432069 : Nat.Prime 31432069 := by
  apply lucas_primality 31432069 (2 : ZMod 31432069)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (873113, 1)] : List FactorBlock).map factorBlockValue).prod) = 31432069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_873113
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 31432069) ^ 15716034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 10477356 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 31432069) ^ 36 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_31969337 : Nat.Prime 31969337 := by
  apply lucas_primality 31969337 (3 : ZMod 31969337)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (7, 1), (570881, 1)] : List FactorBlock).map factorBlockValue).prod) = 31969337 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_570881
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 31969337) ^ 15984668 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 4567048 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 31969337) ^ 56 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_32701811 : Nat.Prime 32701811 := by
  apply lucas_primality 32701811 (2 : ZMod 32701811)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (73, 1), (44797, 1)] : List FactorBlock).map factorBlockValue).prod) = 32701811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_73
      · exact prime_oneHundredTwentySixDT_44797
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 32701811) ^ 16350905 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 6540362 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 447970 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 32701811) ^ 730 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_34355329 : Nat.Prime 34355329 := by
  apply lucas_primality 34355329 (13 : ZMod 34355329)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (7, 1), (12781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (7, 1), (12781, 1)] : List FactorBlock).map factorBlockValue).prod) = 34355329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_12781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 34355329) ^ 17177664 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 34355329) ^ 11451776 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 34355329) ^ 4907904 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 34355329) ^ 2688 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_34858727 : Nat.Prime 34858727 := by
  apply lucas_primality 34858727 (7 : ZMod 34858727)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (2489909, 1)] : List FactorBlock).map factorBlockValue).prod) = 34858727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_2489909
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 34858727) ^ 17429363 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 4979818 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 34858727) ^ 14 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_37097537 : Nat.Prime 37097537 := by
  apply lucas_primality 37097537 (3 : ZMod 37097537)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (7, 1), (17, 1), (4871, 1)] : List FactorBlock).map factorBlockValue).prod) = 37097537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_4871
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 37097537) ^ 18548768 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 5299648 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 2182208 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 37097537) ^ 7616 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_39534697 : Nat.Prime 39534697 := by
  apply lucas_primality 39534697 (7 : ZMod 39534697)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (103, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (103, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) = 39534697 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_103
      · exact prime_oneHundredTwentySixDT_1777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 39534697) ^ 19767348 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 39534697) ^ 13178232 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 39534697) ^ 383832 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 39534697) ^ 22248 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_40674451 : Nat.Prime 40674451 := by
  apply lucas_primality 40674451 (2 : ZMod 40674451)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 2), (271163, 1)] : List FactorBlock).map factorBlockValue).prod) = 40674451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_271163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 40674451) ^ 20337225 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 13558150 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 8134890 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 40674451) ^ 150 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_43156297 : Nat.Prime 43156297 := by
  apply lucas_primality 43156297 (5 : ZMod 43156297)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (19, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (19, 1), (31547, 1)] : List FactorBlock).map factorBlockValue).prod) = 43156297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_31547
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 43156297) ^ 21578148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 43156297) ^ 14385432 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 43156297) ^ 2271384 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 43156297) ^ 1368 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_46313749 : Nat.Prime 46313749 := by
  apply lucas_primality 46313749 (2 : ZMod 46313749)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (13, 1), (32987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (13, 1), (32987, 1)] : List FactorBlock).map factorBlockValue).prod) = 46313749 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_32987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 46313749) ^ 23156874 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46313749) ^ 15437916 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46313749) ^ 3562596 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 46313749) ^ 1404 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_58121429 : Nat.Prime 58121429 := by
  apply lucas_primality 58121429 (2 : ZMod 58121429)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (67, 1), (137, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (67, 1), (137, 1), (1583, 1)] : List FactorBlock).map factorBlockValue).prod) = 58121429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_67
      · exact prime_oneHundredTwentySixDT_137
      · exact prime_oneHundredTwentySixDT_1583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58121429) ^ 29060714 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 867484 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 424244 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58121429) ^ 36716 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_59929613 : Nat.Prime 59929613 := by
  apply lucas_primality 59929613 (2 : ZMod 59929613)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1811, 1), (8273, 1)] : List FactorBlock).map factorBlockValue).prod) = 59929613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1811
      · exact prime_oneHundredTwentySixDT_8273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 59929613) ^ 29964806 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 33092 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59929613) ^ 7244 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_61405583 : Nat.Prime 61405583 := by
  apply lucas_primality 61405583 (5 : ZMod 61405583)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (149, 1), (29437, 1)] : List FactorBlock).map factorBlockValue).prod) = 61405583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_149
      · exact prime_oneHundredTwentySixDT_29437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 61405583) ^ 30702791 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 8772226 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 412118 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 61405583) ^ 2086 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_66909917 : Nat.Prime 66909917 := by
  apply lucas_primality 66909917 (2 : ZMod 66909917)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (16727479, 1)] : List FactorBlock).map factorBlockValue).prod) = 66909917 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_16727479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 66909917) ^ 33454958 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 66909917) ^ 4 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_67498297 : Nat.Prime 67498297 := by
  apply lucas_primality 67498297 (5 : ZMod 67498297)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (17, 1), (165437, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (17, 1), (165437, 1)] : List FactorBlock).map factorBlockValue).prod) = 67498297 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_165437
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 67498297) ^ 33749148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 67498297) ^ 22499432 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 67498297) ^ 3970488 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 67498297) ^ 408 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_68264617 : Nat.Prime 68264617 := by
  apply lucas_primality 68264617 (5 : ZMod 68264617)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (7, 1), (347, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (7, 1), (347, 1), (1171, 1)] : List FactorBlock).map factorBlockValue).prod) = 68264617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_347
      · exact prime_oneHundredTwentySixDT_1171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 68264617) ^ 34132308 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68264617) ^ 22754872 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68264617) ^ 9752088 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68264617) ^ 196728 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 68264617) ^ 58296 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_68430689 : Nat.Prime 68430689 := by
  apply lucas_primality 68430689 (3 : ZMod 68430689)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (631, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (631, 1), (3389, 1)] : List FactorBlock).map factorBlockValue).prod) = 68430689 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_631
      · exact prime_oneHundredTwentySixDT_3389
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 68430689) ^ 34215344 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68430689) ^ 108448 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 68430689) ^ 20192 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_75641231 : Nat.Prime 75641231 := by
  apply lucas_primality 75641231 (7 : ZMod 75641231)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (1080589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (1080589, 1)] : List FactorBlock).map factorBlockValue).prod) = 75641231 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_1080589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 75641231) ^ 37820615 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 75641231) ^ 15128246 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 75641231) ^ 10805890 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 75641231) ^ 70 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_84404381 : Nat.Prime 84404381 := by
  apply lucas_primality 84404381 (2 : ZMod 84404381)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (103, 1), (40973, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (103, 1), (40973, 1)] : List FactorBlock).map factorBlockValue).prod) = 84404381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_103
      · exact prime_oneHundredTwentySixDT_40973
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 84404381) ^ 42202190 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 84404381) ^ 16880876 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 84404381) ^ 819460 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 84404381) ^ 2060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_85339979 : Nat.Prime 85339979 := by
  apply lucas_primality 85339979 (2 : ZMod 85339979)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (233, 1), (367, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (233, 1), (367, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 85339979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_233
      · exact prime_oneHundredTwentySixDT_367
      · exact prime_oneHundredTwentySixDT_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 85339979) ^ 42669989 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 85339979) ^ 366266 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 85339979) ^ 232534 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 85339979) ^ 171022 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_98958901 : Nat.Prime 98958901 := by
  apply lucas_primality 98958901 (6 : ZMod 98958901)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (329863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (329863, 1)] : List FactorBlock).map factorBlockValue).prod) = 98958901 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_329863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 98958901) ^ 49479450 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 32986300 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 19791780 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 98958901) ^ 300 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_126606197 : Nat.Prime 126606197 := by
  apply lucas_primality 126606197 (2 : ZMod 126606197)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (19, 1), (41, 2), (991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (19, 1), (41, 2), (991, 1)] : List FactorBlock).map factorBlockValue).prod) = 126606197 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_41
      · exact prime_oneHundredTwentySixDT_991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 126606197) ^ 63303098 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 126606197) ^ 6663484 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 126606197) ^ 3087956 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 126606197) ^ 127756 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_131433079 : Nat.Prime 131433079 := by
  apply lucas_primality 131433079 (17 : ZMod 131433079)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (223, 1), (14033, 1)] : List FactorBlock).map factorBlockValue).prod) = 131433079 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_223
      · exact prime_oneHundredTwentySixDT_14033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 131433079) ^ 65716539 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 43811026 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 18776154 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 589386 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 131433079) ^ 9366 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_134645171 : Nat.Prime 134645171 := by
  apply lucas_primality 134645171 (6 : ZMod 134645171)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (11, 2), (223, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (11, 2), (223, 1), (499, 1)] : List FactorBlock).map factorBlockValue).prod) = 134645171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_223
      · exact prime_oneHundredTwentySixDT_499
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 134645171) ^ 67322585 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 134645171) ^ 26929034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 134645171) ^ 12240470 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 134645171) ^ 603790 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 134645171) ^ 269830 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_138986321 : Nat.Prime 138986321 := by
  apply lucas_primality 138986321 (6 : ZMod 138986321)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (5, 1), (11, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (5, 1), (11, 1), (43, 1), (3673, 1)] : List FactorBlock).map factorBlockValue).prod) = 138986321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_43
      · exact prime_oneHundredTwentySixDT_3673
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 138986321) ^ 69493160 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 138986321) ^ 27797264 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 138986321) ^ 12635120 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 138986321) ^ 3232240 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 138986321) ^ 37840 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_139568171 : Nat.Prime 139568171 := by
  apply lucas_primality 139568171 (2 : ZMod 139568171)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 2), (284833, 1)] : List FactorBlock).map factorBlockValue).prod) = 139568171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_284833
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 139568171) ^ 69784085 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 27913634 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 19938310 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 139568171) ^ 490 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_158265131 : Nat.Prime 158265131 := by
  apply lucas_primality 158265131 (2 : ZMod 158265131)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (15826513, 1)] : List FactorBlock).map factorBlockValue).prod) = 158265131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_15826513
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 158265131) ^ 79132565 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 31653026 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 158265131) ^ 10 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_165758291 : Nat.Prime 165758291 := by
  apply lucas_primality 165758291 (2 : ZMod 165758291)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (431, 1), (38459, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (431, 1), (38459, 1)] : List FactorBlock).map factorBlockValue).prod) = 165758291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_431
      · exact prime_oneHundredTwentySixDT_38459
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 165758291) ^ 82879145 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 165758291) ^ 33151658 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 165758291) ^ 384590 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 165758291) ^ 4310 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_170301979 : Nat.Prime 170301979 := by
  apply lucas_primality 170301979 (2 : ZMod 170301979)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (11, 1), (19, 1), (29, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (11, 1), (19, 1), (29, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 170301979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 170301979) ^ 85150989 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 56767326 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 24328854 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 15481998 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 8963262 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 5872482 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 170301979) ^ 763686 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_182141261 : Nat.Prime 182141261 := by
  apply lucas_primality 182141261 (10 : ZMod 182141261)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (59, 1), (22051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (59, 1), (22051, 1)] : List FactorBlock).map factorBlockValue).prod) = 182141261 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_59
      · exact prime_oneHundredTwentySixDT_22051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 182141261) ^ 91070630 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 182141261) ^ 36428252 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 182141261) ^ 26020180 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 182141261) ^ 3087140 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 182141261) ^ 8260 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_208604521 : Nat.Prime 208604521 := by
  apply lucas_primality 208604521 (7 : ZMod 208604521)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (5, 1), (37, 1), (15661, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (5, 1), (37, 1), (15661, 1)] : List FactorBlock).map factorBlockValue).prod) = 208604521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_15661
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 208604521) ^ 104302260 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 208604521) ^ 69534840 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 208604521) ^ 41720904 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 208604521) ^ 5637960 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 208604521) ^ 13320 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_217635829 : Nat.Prime 217635829 := by
  apply lucas_primality 217635829 (6 : ZMod 217635829)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (18136319, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (18136319, 1)] : List FactorBlock).map factorBlockValue).prod) = 217635829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_18136319
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (6 : ZMod 217635829) ^ 108817914 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 217635829) ^ 72545276 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 217635829) ^ 12 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_224682253 : Nat.Prime 224682253 := by
  apply lucas_primality 224682253 (2 : ZMod 224682253)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (1861, 1), (10061, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (1861, 1), (10061, 1)] : List FactorBlock).map factorBlockValue).prod) = 224682253 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_1861
      · exact prime_oneHundredTwentySixDT_10061
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 224682253) ^ 112341126 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 74894084 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 120732 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 224682253) ^ 22332 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_233347063 : Nat.Prime 233347063 := by
  apply lucas_primality 233347063 (5 : ZMod 233347063)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2991629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2991629, 1)] : List FactorBlock).map factorBlockValue).prod) = 233347063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_2991629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 233347063) ^ 116673531 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 233347063) ^ 77782354 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 233347063) ^ 17949774 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 233347063) ^ 78 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_237483941 : Nat.Prime 237483941 := by
  apply lucas_primality 237483941 (3 : ZMod 237483941)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11874197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11874197, 1)] : List FactorBlock).map factorBlockValue).prod) = 237483941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_11874197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 237483941) ^ 118741970 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 237483941) ^ 47496788 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 237483941) ^ 20 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_261786659 : Nat.Prime 261786659 := by
  apply lucas_primality 261786659 (2 : ZMod 261786659)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (59, 1), (557, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (59, 1), (557, 1), (569, 1)] : List FactorBlock).map factorBlockValue).prod) = 261786659 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_59
      · exact prime_oneHundredTwentySixDT_557
      · exact prime_oneHundredTwentySixDT_569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 261786659) ^ 130893329 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 261786659) ^ 37398094 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 261786659) ^ 4437062 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 261786659) ^ 469994 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 261786659) ^ 460082 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_278993839 : Nat.Prime 278993839 := by
  apply lucas_primality 278993839 (3 : ZMod 278993839)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (37, 1), (1256729, 1)] : List FactorBlock).map factorBlockValue).prod) = 278993839 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_1256729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 278993839) ^ 139496919 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 92997946 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 7540374 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 278993839) ^ 222 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_286581829 : Nat.Prime 286581829 := by
  apply lucas_primality 286581829 (6 : ZMod 286581829)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (13, 1), (29, 1), (63347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (13, 1), (29, 1), (63347, 1)] : List FactorBlock).map factorBlockValue).prod) = 286581829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_63347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 286581829) ^ 143290914 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 95527276 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 22044756 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 9882132 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 286581829) ^ 4524 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_288092947 : Nat.Prime 288092947 := by
  apply lucas_primality 288092947 (2 : ZMod 288092947)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (6833, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (6833, 1), (7027, 1)] : List FactorBlock).map factorBlockValue).prod) = 288092947 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_6833
      · exact prime_oneHundredTwentySixDT_7027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 288092947) ^ 144046473 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 288092947) ^ 96030982 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 288092947) ^ 42162 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 288092947) ^ 40998 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_292202129 : Nat.Prime 292202129 := by
  apply lucas_primality 292202129 (3 : ZMod 292202129)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (18262633, 1)] : List FactorBlock).map factorBlockValue).prod) = 292202129 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_18262633
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 292202129) ^ 146101064 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 292202129) ^ 16 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_327359309 : Nat.Prime 327359309 := by
  apply lucas_primality 327359309 (2 : ZMod 327359309)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (29, 1), (137, 1), (20599, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (29, 1), (137, 1), (20599, 1)] : List FactorBlock).map factorBlockValue).prod) = 327359309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_137
      · exact prime_oneHundredTwentySixDT_20599
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 327359309) ^ 163679654 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 327359309) ^ 11288252 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 327359309) ^ 2389484 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 327359309) ^ 15892 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_331516583 : Nat.Prime 331516583 := by
  apply lucas_primality 331516583 (5 : ZMod 331516583)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (165758291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (165758291, 1)] : List FactorBlock).map factorBlockValue).prod) = 331516583 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_165758291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 331516583) ^ 165758291 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 331516583) ^ 2 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_429453131 : Nat.Prime 429453131 := by
  apply lucas_primality 429453131 (2 : ZMod 429453131)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (2311, 1), (18583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (2311, 1), (18583, 1)] : List FactorBlock).map factorBlockValue).prod) = 429453131 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_2311
      · exact prime_oneHundredTwentySixDT_18583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 429453131) ^ 214726565 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 429453131) ^ 85890626 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 429453131) ^ 185830 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 429453131) ^ 23110 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_525505291 : Nat.Prime 525505291 := by
  apply lucas_primality 525505291 (2 : ZMod 525505291)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (17516843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (17516843, 1)] : List FactorBlock).map factorBlockValue).prod) = 525505291 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_17516843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 525505291) ^ 262752645 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 525505291) ^ 175168430 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 525505291) ^ 105101058 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 525505291) ^ 30 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_545326447 : Nat.Prime 545326447 := by
  apply lucas_primality 545326447 (6 : ZMod 545326447)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (12983963, 1)] : List FactorBlock).map factorBlockValue).prod) = 545326447 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_12983963
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 545326447) ^ 272663223 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 181775482 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 77903778 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 545326447) ^ 42 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_596250997 : Nat.Prime 596250997 := by
  apply lucas_primality 596250997 (5 : ZMod 596250997)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (17, 1), (265709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (17, 1), (265709, 1)] : List FactorBlock).map factorBlockValue).prod) = 596250997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_265709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 596250997) ^ 298125498 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 198750332 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 54204636 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 35073588 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 596250997) ^ 2244 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_597092591 : Nat.Prime 597092591 := by
  apply lucas_primality 597092591 (14 : ZMod 597092591)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (1013, 1), (58943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (1013, 1), (58943, 1)] : List FactorBlock).map factorBlockValue).prod) = 597092591 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_1013
      · exact prime_oneHundredTwentySixDT_58943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (14 : ZMod 597092591) ^ 298546295 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 597092591) ^ 119418518 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 597092591) ^ 589430 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 597092591) ^ 10130 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_640433267 : Nat.Prime 640433267 := by
  apply lucas_primality 640433267 (2 : ZMod 640433267)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (19, 1), (61, 1), (25117, 1)] : List FactorBlock).map factorBlockValue).prod) = 640433267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_61
      · exact prime_oneHundredTwentySixDT_25117
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 640433267) ^ 320216633 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 58221206 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 33707014 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 10498906 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 640433267) ^ 25498 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_679475179 : Nat.Prime 679475179 := by
  apply lucas_primality 679475179 (10 : ZMod 679475179)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (37, 1), (1020233, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (37, 1), (1020233, 1)] : List FactorBlock).map factorBlockValue).prod) = 679475179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_1020233
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 679475179) ^ 339737589 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 679475179) ^ 226491726 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 679475179) ^ 18364194 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 679475179) ^ 666 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_714027719 : Nat.Prime 714027719 := by
  apply lucas_primality 714027719 (11 : ZMod 714027719)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17203, 1), (20753, 1)] : List FactorBlock).map factorBlockValue).prod) = 714027719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_17203
      · exact prime_oneHundredTwentySixDT_20753
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (11 : ZMod 714027719) ^ 357013859 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 41506 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 714027719) ^ 34406 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_732506743 : Nat.Prime 732506743 := by
  apply lucas_primality 732506743 (19 : ZMod 732506743)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (11, 1), (101, 1), (36629, 1)] : List FactorBlock).map factorBlockValue).prod) = 732506743 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_101
      · exact prime_oneHundredTwentySixDT_36629
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 732506743) ^ 366253371 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 244168914 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 66591522 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 7252542 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 732506743) ^ 19998 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_738048887 : Nat.Prime 738048887 := by
  apply lucas_primality 738048887 (5 : ZMod 738048887)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (16044541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (16044541, 1)] : List FactorBlock).map factorBlockValue).prod) = 738048887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_16044541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 738048887) ^ 369024443 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 738048887) ^ 32089082 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 738048887) ^ 46 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_759567493 : Nat.Prime 759567493 := by
  apply lucas_primality 759567493 (5 : ZMod 759567493)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (21099097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (21099097, 1)] : List FactorBlock).map factorBlockValue).prod) = 759567493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_21099097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 759567493) ^ 379783746 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 759567493) ^ 253189164 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 759567493) ^ 36 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_810060997 : Nat.Prime 810060997 := by
  apply lucas_primality 810060997 (2 : ZMod 810060997)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (821, 1), (82223, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (821, 1), (82223, 1)] : List FactorBlock).map factorBlockValue).prod) = 810060997 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_821
      · exact prime_oneHundredTwentySixDT_82223
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 810060997) ^ 405030498 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810060997) ^ 270020332 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810060997) ^ 986676 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 810060997) ^ 9852 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_906208483 : Nat.Prime 906208483 := by
  apply lucas_primality 906208483 (2 : ZMod 906208483)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (131, 1), (1152937, 1)] : List FactorBlock).map factorBlockValue).prod) = 906208483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_131
      · exact prime_oneHundredTwentySixDT_1152937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 906208483) ^ 453104241 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 302069494 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 6917622 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 906208483) ^ 786 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_945329461 : Nat.Prime 945329461 := by
  apply lucas_primality 945329461 (2 : ZMod 945329461)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (151, 2), (691, 1)] : List FactorBlock).map factorBlockValue).prod) = 945329461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_151
      · exact prime_oneHundredTwentySixDT_691
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 945329461) ^ 472664730 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 315109820 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 189065892 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 6260460 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 945329461) ^ 1368060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_977396369 : Nat.Prime 977396369 := by
  apply lucas_primality 977396369 (3 : ZMod 977396369)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (17, 1), (263, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (17, 1), (263, 1), (1051, 1)] : List FactorBlock).map factorBlockValue).prod) = 977396369 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_263
      · exact prime_oneHundredTwentySixDT_1051
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 977396369) ^ 488698184 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 977396369) ^ 75184336 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 977396369) ^ 57493904 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 977396369) ^ 3716336 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 977396369) ^ 929968 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1002450643 : Nat.Prime 1002450643 := by
  apply lucas_primality 1002450643 (2 : ZMod 1002450643)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1567, 1), (106621, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1567, 1), (106621, 1)] : List FactorBlock).map factorBlockValue).prod) = 1002450643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_1567
      · exact prime_oneHundredTwentySixDT_106621
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1002450643) ^ 501225321 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1002450643) ^ 334150214 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1002450643) ^ 639726 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1002450643) ^ 9402 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1057169473 : Nat.Prime 1057169473 := by
  apply lucas_primality 1057169473 (7 : ZMod 1057169473)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (5506091, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (5506091, 1)] : List FactorBlock).map factorBlockValue).prod) = 1057169473 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5506091
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1057169473) ^ 528584736 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1057169473) ^ 352389824 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1057169473) ^ 192 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1101126877 : Nat.Prime 1101126877 := by
  apply lucas_primality 1101126877 (2 : ZMod 1101126877)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (457, 1), (200789, 1)] : List FactorBlock).map factorBlockValue).prod) = 1101126877 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_457
      · exact prime_oneHundredTwentySixDT_200789
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1101126877) ^ 550563438 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 367042292 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 2409468 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1101126877) ^ 5484 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1194185183 : Nat.Prime 1194185183 := by
  apply lucas_primality 1194185183 (5 : ZMod 1194185183)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (597092591, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (597092591, 1)] : List FactorBlock).map factorBlockValue).prod) = 1194185183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_597092591
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (5 : ZMod 1194185183) ^ 597092591 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1194185183) ^ 2 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1336248751 : Nat.Prime 1336248751 := by
  apply lucas_primality 1336248751 (3 : ZMod 1336248751)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 4), (356333, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 4), (356333, 1)] : List FactorBlock).map factorBlockValue).prod) = 1336248751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_356333
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1336248751) ^ 668124375 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1336248751) ^ 445416250 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1336248751) ^ 267249750 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1336248751) ^ 3750 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1344571663 : Nat.Prime 1344571663 := by
  apply lucas_primality 1344571663 (6 : ZMod 1344571663)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 3), (653339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 3), (653339, 1)] : List FactorBlock).map factorBlockValue).prod) = 1344571663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_653339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1344571663) ^ 672285831 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1344571663) ^ 448190554 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1344571663) ^ 192081666 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1344571663) ^ 2058 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1468819613 : Nat.Prime 1468819613 := by
  apply lucas_primality 1468819613 (2 : ZMod 1468819613)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (28246531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (28246531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1468819613 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_28246531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 1468819613) ^ 734409806 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1468819613) ^ 112986124 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1468819613) ^ 52 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1587826921 : Nat.Prime 1587826921 := by
  apply lucas_primality 1587826921 (11 : ZMod 1587826921)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (13231891, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (13231891, 1)] : List FactorBlock).map factorBlockValue).prod) = 1587826921 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13231891
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (11 : ZMod 1587826921) ^ 793913460 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1587826921) ^ 529275640 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1587826921) ^ 317565384 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 1587826921) ^ 120 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1706007343 : Nat.Prime 1706007343 := by
  apply lucas_primality 1706007343 (3 : ZMod 1706007343)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 2), (251, 1), (6703, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 2), (251, 1), (6703, 1)] : List FactorBlock).map factorBlockValue).prod) = 1706007343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_251
      · exact prime_oneHundredTwentySixDT_6703
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1706007343) ^ 853003671 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706007343) ^ 568669114 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706007343) ^ 131231334 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706007343) ^ 6796842 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1706007343) ^ 254514 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1956927067 : Nat.Prime 1956927067 := by
  apply lucas_primality 1956927067 (3 : ZMod 1956927067)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (107, 1), (3048173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (107, 1), (3048173, 1)] : List FactorBlock).map factorBlockValue).prod) = 1956927067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_107
      · exact prime_oneHundredTwentySixDT_3048173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1956927067) ^ 978463533 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956927067) ^ 652309022 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956927067) ^ 18289038 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1956927067) ^ 642 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2016230959 : Nat.Prime 2016230959 := by
  apply lucas_primality 2016230959 (3 : ZMod 2016230959)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (229, 1), (69877, 1)] : List FactorBlock).map factorBlockValue).prod) = 2016230959 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_229
      · exact prime_oneHundredTwentySixDT_69877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2016230959) ^ 1008115479 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 672076986 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 288032994 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 8804502 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2016230959) ^ 28854 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2027955593 : Nat.Prime 2027955593 := by
  apply lucas_primality 2027955593 (3 : ZMod 2027955593)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (107, 1), (182239, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (107, 1), (182239, 1)] : List FactorBlock).map factorBlockValue).prod) = 2027955593 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_107
      · exact prime_oneHundredTwentySixDT_182239
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2027955593) ^ 1013977796 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2027955593) ^ 155996584 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2027955593) ^ 18952856 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2027955593) ^ 11128 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2165692049 : Nat.Prime 2165692049 := by
  apply lucas_primality 2165692049 (3 : ZMod 2165692049)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (13, 1), (19, 1), (547999, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (13, 1), (19, 1), (547999, 1)] : List FactorBlock).map factorBlockValue).prod) = 2165692049 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_547999
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 2165692049) ^ 1082846024 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 166591696 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 113983792 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2165692049) ^ 3952 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2235374311 : Nat.Prime 2235374311 := by
  apply lucas_primality 2235374311 (3 : ZMod 2235374311)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (13, 1), (5731729, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (13, 1), (5731729, 1)] : List FactorBlock).map factorBlockValue).prod) = 2235374311 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_5731729
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2235374311) ^ 1117687155 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2235374311) ^ 745124770 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2235374311) ^ 447074862 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2235374311) ^ 171951870 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2235374311) ^ 390 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2439250031 : Nat.Prime 2439250031 := by
  apply lucas_primality 2439250031 (7 : ZMod 2439250031)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (29, 1), (1201601, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (29, 1), (1201601, 1)] : List FactorBlock).map factorBlockValue).prod) = 2439250031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_1201601
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 2439250031) ^ 1219625015 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2439250031) ^ 487850006 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2439250031) ^ 348464290 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2439250031) ^ 84112070 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 2439250031) ^ 2030 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2444182381 : Nat.Prime 2444182381 := by
  apply lucas_primality 2444182381 (2 : ZMod 2444182381)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 1), (59, 1), (230149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 1), (59, 1), (230149, 1)] : List FactorBlock).map factorBlockValue).prod) = 2444182381 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_59
      · exact prime_oneHundredTwentySixDT_230149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2444182381) ^ 1222091190 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2444182381) ^ 814727460 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2444182381) ^ 488836476 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2444182381) ^ 41426820 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2444182381) ^ 10620 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2676584257 : Nat.Prime 2676584257 := by
  apply lucas_primality 2676584257 (5 : ZMod 2676584257)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 1), (13940543, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 1), (13940543, 1)] : List FactorBlock).map factorBlockValue).prod) = 2676584257 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13940543
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 2676584257) ^ 1338292128 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2676584257) ^ 892194752 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2676584257) ^ 192 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2933617829 : Nat.Prime 2933617829 := by
  apply lucas_primality 2933617829 (2 : ZMod 2933617829)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1787, 1), (410411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1787, 1), (410411, 1)] : List FactorBlock).map factorBlockValue).prod) = 2933617829 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1787
      · exact prime_oneHundredTwentySixDT_410411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2933617829) ^ 1466808914 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933617829) ^ 1641644 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2933617829) ^ 7148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3421534451 : Nat.Prime 3421534451 := by
  apply lucas_primality 3421534451 (2 : ZMod 3421534451)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (68430689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (68430689, 1)] : List FactorBlock).map factorBlockValue).prod) = 3421534451 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_68430689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3421534451) ^ 1710767225 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3421534451) ^ 684306890 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3421534451) ^ 50 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3733553009 : Nat.Prime 3733553009 := by
  apply lucas_primality 3733553009 (3 : ZMod 3733553009)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (233347063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (233347063, 1)] : List FactorBlock).map factorBlockValue).prod) = 3733553009 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_233347063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 3733553009) ^ 1866776504 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3733553009) ^ 16 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4827581489 : Nat.Prime 4827581489 := by
  apply lucas_primality 4827581489 (6 : ZMod 4827581489)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (107, 1), (499, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (107, 1), (499, 1), (5651, 1)] : List FactorBlock).map factorBlockValue).prod) = 4827581489 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_107
      · exact prime_oneHundredTwentySixDT_499
      · exact prime_oneHundredTwentySixDT_5651
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 4827581489) ^ 2413790744 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4827581489) ^ 45117584 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4827581489) ^ 9674512 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4827581489) ^ 854288 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5276183617 : Nat.Prime 5276183617 := by
  apply lucas_primality 5276183617 (7 : ZMod 5276183617)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 6), (3, 3), (11, 1), (277577, 1)] : List FactorBlock).map factorBlockValue).prod) = 5276183617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_277577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 5276183617) ^ 2638091808 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 1758727872 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 479653056 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 5276183617) ^ 19008 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5378286653 : Nat.Prime 5378286653 := by
  apply lucas_primality 5378286653 (2 : ZMod 5378286653)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1344571663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1344571663, 1)] : List FactorBlock).map factorBlockValue).prod) = 5378286653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1344571663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 5378286653) ^ 2689143326 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5378286653) ^ 4 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5605209397 : Nat.Prime 5605209397 := by
  apply lucas_primality 5605209397 (2 : ZMod 5605209397)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 4), (2543, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 4), (2543, 1), (6803, 1)] : List FactorBlock).map factorBlockValue).prod) = 5605209397 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_2543
      · exact prime_oneHundredTwentySixDT_6803
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 5605209397) ^ 2802604698 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5605209397) ^ 1868403132 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5605209397) ^ 2204172 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5605209397) ^ 823932 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6037638679 : Nat.Prime 6037638679 := by
  apply lucas_primality 6037638679 (3 : ZMod 6037638679)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (31, 1), (10820141, 1)] : List FactorBlock).map factorBlockValue).prod) = 6037638679 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_31
      · exact prime_oneHundredTwentySixDT_10820141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 6037638679) ^ 3018819339 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 2012546226 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 194762538 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6037638679) ^ 558 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6393737663 : Nat.Prime 6393737663 := by
  apply lucas_primality 6393737663 (5 : ZMod 6393737663)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (23, 1), (31, 1), (311, 1), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 6393737663 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_31
      · exact prime_oneHundredTwentySixDT_311
      · exact prime_oneHundredTwentySixDT_1109
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6393737663) ^ 3196868831 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 491825974 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 277988594 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 206249602 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 20558642 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6393737663) ^ 5765318 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_7062147991 : Nat.Prime 7062147991 := by
  apply lucas_primality 7062147991 (6 : ZMod 7062147991)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (17, 1), (4615783, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (17, 1), (4615783, 1)] : List FactorBlock).map factorBlockValue).prod) = 7062147991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_4615783
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 7062147991) ^ 3531073995 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 7062147991) ^ 2354049330 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 7062147991) ^ 1412429598 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 7062147991) ^ 415420470 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 7062147991) ^ 1530 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_7467106019 : Nat.Prime 7467106019 := by
  apply lucas_primality 7467106019 (2 : ZMod 7467106019)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3733553009, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3733553009, 1)] : List FactorBlock).map factorBlockValue).prod) = 7467106019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3733553009
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 7467106019) ^ 3733553009 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7467106019) ^ 2 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_8063847427 : Nat.Prime 8063847427 := by
  apply lucas_primality 8063847427 (3 : ZMod 8063847427)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (1531, 1), (38167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (1531, 1), (38167, 1)] : List FactorBlock).map factorBlockValue).prod) = 8063847427 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_1531
      · exact prime_oneHundredTwentySixDT_38167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 8063847427) ^ 4031923713 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8063847427) ^ 2687949142 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8063847427) ^ 350602062 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8063847427) ^ 5267046 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 8063847427) ^ 211278 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_8088852907 : Nat.Prime 8088852907 := by
  apply lucas_primality 8088852907 (2 : ZMod 8088852907)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (61, 1), (7366897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (61, 1), (7366897, 1)] : List FactorBlock).map factorBlockValue).prod) = 8088852907 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_61
      · exact prime_oneHundredTwentySixDT_7366897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 8088852907) ^ 4044426453 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8088852907) ^ 2696284302 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8088852907) ^ 132604146 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8088852907) ^ 1098 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_9013747499 : Nat.Prime 9013747499 := by
  apply lucas_primality 9013747499 (2 : ZMod 9013747499)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (4937, 1), (130411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (4937, 1), (130411, 1)] : List FactorBlock).map factorBlockValue).prod) = 9013747499 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_4937
      · exact prime_oneHundredTwentySixDT_130411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 9013747499) ^ 4506873749 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013747499) ^ 1287678214 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013747499) ^ 1825754 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9013747499) ^ 69118 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_9299447551 : Nat.Prime 9299447551 := by
  apply lucas_primality 9299447551 (3 : ZMod 9299447551)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 2), (157, 1), (131627, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 2), (157, 1), (131627, 1)] : List FactorBlock).map factorBlockValue).prod) = 9299447551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_157
      · exact prime_oneHundredTwentySixDT_131627
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9299447551) ^ 4649723775 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 3099815850 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 1859889510 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 59232150 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9299447551) ^ 70650 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_10706337029 : Nat.Prime 10706337029 := by
  apply lucas_primality 10706337029 (2 : ZMod 10706337029)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (2676584257, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (2676584257, 1)] : List FactorBlock).map factorBlockValue).prod) = 10706337029 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_2676584257
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10706337029) ^ 5353168514 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10706337029) ^ 4 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_10756573307 : Nat.Prime 10756573307 := by
  apply lucas_primality 10756573307 (2 : ZMod 10756573307)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5378286653, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5378286653, 1)] : List FactorBlock).map factorBlockValue).prod) = 10756573307 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5378286653
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 10756573307) ^ 5378286653 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10756573307) ^ 2 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_11440553653 : Nat.Prime 11440553653 := by
  apply lucas_primality 11440553653 (2 : ZMod 11440553653)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11, 1), (263, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11, 1), (263, 1), (109849, 1)] : List FactorBlock).map factorBlockValue).prod) = 11440553653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_263
      · exact prime_oneHundredTwentySixDT_109849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11440553653) ^ 5720276826 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 3813517884 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 1040050332 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 43500204 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11440553653) ^ 104148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_11653114643 : Nat.Prime 11653114643 := by
  apply lucas_primality 11653114643 (2 : ZMod 11653114643)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (311, 1), (811, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (311, 1), (811, 1), (1777, 1)] : List FactorBlock).map factorBlockValue).prod) = 11653114643 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_311
      · exact prime_oneHundredTwentySixDT_811
      · exact prime_oneHundredTwentySixDT_1777
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 11653114643) ^ 5826557321 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11653114643) ^ 896393434 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11653114643) ^ 37469822 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11653114643) ^ 14368822 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 11653114643) ^ 6557746 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_12608531843 : Nat.Prime 12608531843 := by
  apply lucas_primality 12608531843 (2 : ZMod 12608531843)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (43117, 1), (146213, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (43117, 1), (146213, 1)] : List FactorBlock).map factorBlockValue).prod) = 12608531843 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_43117
      · exact prime_oneHundredTwentySixDT_146213
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12608531843) ^ 6304265921 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12608531843) ^ 292426 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12608531843) ^ 86234 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_13460448439 : Nat.Prime 13460448439 := by
  apply lucas_primality 13460448439 (3 : ZMod 13460448439)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (433, 1), (677, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (433, 1), (677, 1), (2551, 1)] : List FactorBlock).map factorBlockValue).prod) = 13460448439 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_433
      · exact prime_oneHundredTwentySixDT_677
      · exact prime_oneHundredTwentySixDT_2551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 13460448439) ^ 6730224219 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 13460448439) ^ 4486816146 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 13460448439) ^ 31086486 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 13460448439) ^ 19882494 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 13460448439) ^ 5276538 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_14026408709 : Nat.Prime 14026408709 := by
  apply lucas_primality 14026408709 (2 : ZMod 14026408709)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (83, 1), (3249863, 1)] : List FactorBlock).map factorBlockValue).prod) = 14026408709 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_83
      · exact prime_oneHundredTwentySixDT_3249863
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 14026408709) ^ 7013204354 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 1078954516 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 168992876 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14026408709) ^ 4316 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_15638890609 : Nat.Prime 15638890609 := by
  apply lucas_primality 15638890609 (14 : ZMod 15638890609)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (11, 1), (89, 1), (110933, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (11, 1), (89, 1), (110933, 1)] : List FactorBlock).map factorBlockValue).prod) = 15638890609 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_110933
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 15638890609) ^ 7819445304 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 15638890609) ^ 5212963536 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 15638890609) ^ 1421717328 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 15638890609) ^ 175717872 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 15638890609) ^ 140976 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_20288258719 : Nat.Prime 20288258719 := by
  apply lucas_primality 20288258719 (3 : ZMod 20288258719)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (13, 1), (461, 1), (80603, 1)] : List FactorBlock).map factorBlockValue).prod) = 20288258719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_461
      · exact prime_oneHundredTwentySixDT_80603
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 20288258719) ^ 10144129359 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 6762752906 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 2898322674 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 1560635286 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 44009238 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 20288258719) ^ 251706 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_23046330287 : Nat.Prime 23046330287 := by
  apply lucas_primality 23046330287 (7 : ZMod 23046330287)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (173, 1), (1583, 1), (6011, 1)] : List FactorBlock).map factorBlockValue).prod) = 23046330287 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_173
      · exact prime_oneHundredTwentySixDT_1583
      · exact prime_oneHundredTwentySixDT_6011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 23046330287) ^ 11523165143 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3292332898 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 133215782 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 14558642 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 23046330287) ^ 3834026 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_23274801787 : Nat.Prime 23274801787 := by
  apply lucas_primality 23274801787 (2 : ZMod 23274801787)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (3541, 1), (1095491, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (3541, 1), (1095491, 1)] : List FactorBlock).map factorBlockValue).prod) = 23274801787 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_3541
      · exact prime_oneHundredTwentySixDT_1095491
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 23274801787) ^ 11637400893 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 23274801787) ^ 7758267262 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 23274801787) ^ 6572946 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 23274801787) ^ 21246 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_24570248051 : Nat.Prime 24570248051 := by
  apply lucas_primality 24570248051 (10 : ZMod 24570248051)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (19, 1), (25863419, 1)] : List FactorBlock).map factorBlockValue).prod) = 24570248051 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_25863419
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 24570248051) ^ 12285124025 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 4914049610 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 1293170950 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 24570248051) ^ 950 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_25790344861 : Nat.Prime 25790344861 := by
  apply lucas_primality 25790344861 (2 : ZMod 25790344861)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 1), (61405583, 1)] : List FactorBlock).map factorBlockValue).prod) = 25790344861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_61405583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25790344861) ^ 12895172430 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 8596781620 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 5158068972 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 3684334980 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25790344861) ^ 420 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_33526403551 : Nat.Prime 33526403551 := by
  apply lucas_primality 33526403551 (6 : ZMod 33526403551)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 2), (673, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 2), (673, 1), (36901, 1)] : List FactorBlock).map factorBlockValue).prod) = 33526403551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_673
      · exact prime_oneHundredTwentySixDT_36901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 33526403551) ^ 16763201775 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33526403551) ^ 11175467850 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33526403551) ^ 6705280710 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33526403551) ^ 49816350 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 33526403551) ^ 908550 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_33883770383 : Nat.Prime 33883770383 := by
  apply lucas_primality 33883770383 (5 : ZMod 33883770383)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (11, 1), (31432069, 1)] : List FactorBlock).map factorBlockValue).prod) = 33883770383 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_31432069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 33883770383) ^ 16941885191 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 4840538626 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 3080342762 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 33883770383) ^ 1078 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_39247588321 : Nat.Prime 39247588321 := by
  apply lucas_primality 39247588321 (13 : ZMod 39247588321)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (5, 1), (643, 1), (127163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (5, 1), (643, 1), (127163, 1)] : List FactorBlock).map factorBlockValue).prod) = 39247588321 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_643
      · exact prime_oneHundredTwentySixDT_127163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 39247588321) ^ 19623794160 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 39247588321) ^ 13082529440 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 39247588321) ^ 7849517664 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 39247588321) ^ 61038240 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 39247588321) ^ 308640 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_44985986047 : Nat.Prime 44985986047 := by
  apply lucas_primality 44985986047 (3 : ZMod 44985986047)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (43, 1), (58121429, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (43, 1), (58121429, 1)] : List FactorBlock).map factorBlockValue).prod) = 44985986047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_43
      · exact prime_oneHundredTwentySixDT_58121429
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 44985986047) ^ 22492993023 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 14995328682 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 1046185722 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 44985986047) ^ 774 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_45636734023 : Nat.Prime 45636734023 := by
  apply lucas_primality 45636734023 (6 : ZMod 45636734023)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (17, 1), (40674451, 1)] : List FactorBlock).map factorBlockValue).prod) = 45636734023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_40674451
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 45636734023) ^ 22818367011 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 15212244674 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 4148794002 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 2684513766 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 45636734023) ^ 1122 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_47612156521 : Nat.Prime 47612156521 := by
  apply lucas_primality 47612156521 (7 : ZMod 47612156521)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (83, 1), (4780337, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (83, 1), (4780337, 1)] : List FactorBlock).map factorBlockValue).prod) = 47612156521 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_83
      · exact prime_oneHundredTwentySixDT_4780337
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 47612156521) ^ 23806078260 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47612156521) ^ 15870718840 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47612156521) ^ 9522431304 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47612156521) ^ 573640440 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 47612156521) ^ 9960 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_59000160181 : Nat.Prime 59000160181 := by
  apply lucas_primality 59000160181 (2 : ZMod 59000160181)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (75641231, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (75641231, 1)] : List FactorBlock).map factorBlockValue).prod) = 59000160181 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_75641231
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 59000160181) ^ 29500080090 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59000160181) ^ 19666720060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59000160181) ^ 11800032036 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59000160181) ^ 4538473860 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 59000160181) ^ 780 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_65139758587 : Nat.Prime 65139758587 := by
  apply lucas_primality 65139758587 (2 : ZMod 65139758587)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (7477, 1), (69143, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (7477, 1), (69143, 1)] : List FactorBlock).map factorBlockValue).prod) = 65139758587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_7477
      · exact prime_oneHundredTwentySixDT_69143
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 65139758587) ^ 32569879293 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65139758587) ^ 21713252862 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65139758587) ^ 9305679798 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65139758587) ^ 8712018 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 65139758587) ^ 942102 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_113168924711 : Nat.Prime 113168924711 := by
  apply lucas_primality 113168924711 (13 : ZMod 113168924711)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (251, 1), (5189, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (251, 1), (5189, 1), (8689, 1)] : List FactorBlock).map factorBlockValue).prod) = 113168924711 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_251
      · exact prime_oneHundredTwentySixDT_5189
      · exact prime_oneHundredTwentySixDT_8689
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 113168924711) ^ 56584462355 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 22633784942 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 450872210 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 21809390 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 113168924711) ^ 13024390 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_128278847423 : Nat.Prime 128278847423 := by
  apply lucas_primality 128278847423 (5 : ZMod 128278847423)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (163, 1), (991, 1), (36097, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (163, 1), (991, 1), (36097, 1)] : List FactorBlock).map factorBlockValue).prod) = 128278847423 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_163
      · exact prime_oneHundredTwentySixDT_991
      · exact prime_oneHundredTwentySixDT_36097
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 128278847423) ^ 64139423711 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 128278847423) ^ 11661713402 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 128278847423) ^ 786986794 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 128278847423) ^ 129443842 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 128278847423) ^ 3553726 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_143866986457 : Nat.Prime 143866986457 := by
  apply lucas_primality 143866986457 (5 : ZMod 143866986457)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (797, 1), (7521277, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (797, 1), (7521277, 1)] : List FactorBlock).map factorBlockValue).prod) = 143866986457 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_797
      · exact prime_oneHundredTwentySixDT_7521277
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 143866986457) ^ 71933493228 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 143866986457) ^ 47955662152 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 143866986457) ^ 180510648 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 143866986457) ^ 19128 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_155440836073 : Nat.Prime 155440836073 := by
  apply lucas_primality 155440836073 (5 : ZMod 155440836073)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 2), (89, 1), (373, 1), (65033, 1)] : List FactorBlock).map factorBlockValue).prod) = 155440836073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_373
      · exact prime_oneHundredTwentySixDT_65033
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 155440836073) ^ 77720418036 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 51813612024 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 1746526248 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 416731464 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 155440836073) ^ 2390184 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_157705373099 : Nat.Prime 157705373099 := by
  apply lucas_primality 157705373099 (2 : ZMod 157705373099)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (13, 1), (71, 1), (1743487, 1)] : List FactorBlock).map factorBlockValue).prod) = 157705373099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_71
      · exact prime_oneHundredTwentySixDT_1743487
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 157705373099) ^ 78852686549 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 22529339014 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 12131182546 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 2221202438 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 157705373099) ^ 90454 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_204046262249 : Nat.Prime 204046262249 := by
  apply lucas_primality 204046262249 (3 : ZMod 204046262249)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (89, 1), (286581829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (89, 1), (286581829, 1)] : List FactorBlock).map factorBlockValue).prod) = 204046262249 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_286581829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 204046262249) ^ 102023131124 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 204046262249) ^ 2292654632 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 204046262249) ^ 712 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_243364641461 : Nat.Prime 243364641461 := by
  apply lucas_primality 243364641461 (2 : ZMod 243364641461)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (19, 1), (640433267, 1)] : List FactorBlock).map factorBlockValue).prod) = 243364641461 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_640433267
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243364641461) ^ 121682320730 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 48672928292 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 12808665340 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243364641461) ^ 380 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_243420692987 : Nat.Prime 243420692987 := by
  apply lucas_primality 243420692987 (2 : ZMod 243420692987)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1283, 1), (3637, 1), (26083, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1283, 1), (3637, 1), (26083, 1)] : List FactorBlock).map factorBlockValue).prod) = 243420692987 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1283
      · exact prime_oneHundredTwentySixDT_3637
      · exact prime_oneHundredTwentySixDT_26083
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 243420692987) ^ 121710346493 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 189727742 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 66928978 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 243420692987) ^ 9332542 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_284071622563 : Nat.Prime 284071622563 := by
  apply lucas_primality 284071622563 (2 : ZMod 284071622563)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (7, 1), (13, 1), (191, 1), (302663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (7, 1), (13, 1), (191, 1), (302663, 1)] : List FactorBlock).map factorBlockValue).prod) = 284071622563 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_191
      · exact prime_oneHundredTwentySixDT_302663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 284071622563) ^ 142035811281 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 284071622563) ^ 94690540854 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 284071622563) ^ 40581660366 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 284071622563) ^ 21851663274 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 284071622563) ^ 1487285982 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 284071622563) ^ 938574 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_343588771969 : Nat.Prime 343588771969 := by
  apply lucas_primality 343588771969 (31 : ZMod 343588771969)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 1), (13, 1), (3931, 1), (17509, 1)] : List FactorBlock).map factorBlockValue).prod) = 343588771969 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_3931
      · exact prime_oneHundredTwentySixDT_17509
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (31 : ZMod 343588771969) ^ 171794385984 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 114529590656 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 26429905536 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 87404928 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (31 : ZMod 343588771969) ^ 19623552 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_354000961087 : Nat.Prime 354000961087 := by
  apply lucas_primality 354000961087 (3 : ZMod 354000961087)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (59000160181, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (59000160181, 1)] : List FactorBlock).map factorBlockValue).prod) = 354000961087 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_59000160181
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 354000961087) ^ 177000480543 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 354000961087) ^ 118000320362 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 354000961087) ^ 6 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_419512127149 : Nat.Prime 419512127149 := by
  apply lucas_primality 419512127149 (7 : ZMod 419512127149)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (11653114643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (11653114643, 1)] : List FactorBlock).map factorBlockValue).prod) = 419512127149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11653114643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 419512127149) ^ 209756063574 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 419512127149) ^ 139837375716 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 419512127149) ^ 36 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_425870674531 : Nat.Prime 425870674531 := by
  apply lucas_primality 425870674531 (2 : ZMod 425870674531)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (7, 1), (2027955593, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (7, 1), (2027955593, 1)] : List FactorBlock).map factorBlockValue).prod) = 425870674531 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_2027955593
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 425870674531) ^ 212935337265 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 425870674531) ^ 141956891510 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 425870674531) ^ 85174134906 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 425870674531) ^ 60838667790 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 425870674531) ^ 210 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_476504362661 : Nat.Prime 476504362661 := by
  apply lucas_primality 476504362661 (2 : ZMod 476504362661)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (139, 1), (2113, 1), (81119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (139, 1), (2113, 1), (81119, 1)] : List FactorBlock).map factorBlockValue).prod) = 476504362661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_139
      · exact prime_oneHundredTwentySixDT_2113
      · exact prime_oneHundredTwentySixDT_81119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 476504362661) ^ 238252181330 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 476504362661) ^ 95300872532 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 476504362661) ^ 3428088940 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 476504362661) ^ 225510820 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 476504362661) ^ 5874140 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_674756143339 : Nat.Prime 674756143339 := by
  apply lucas_primality 674756143339 (3 : ZMod 674756143339)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (67, 2), (313, 1), (80039, 1)] : List FactorBlock).map factorBlockValue).prod) = 674756143339 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_67
      · exact prime_oneHundredTwentySixDT_313
      · exact prime_oneHundredTwentySixDT_80039
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 674756143339) ^ 337378071669 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 224918714446 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 10070987214 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 2155770426 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 674756143339) ^ 8430342 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_704068278961 : Nat.Prime 704068278961 := by
  apply lucas_primality 704068278961 (13 : ZMod 704068278961)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 1), (5, 1), (2933617829, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 1), (5, 1), (2933617829, 1)] : List FactorBlock).map factorBlockValue).prod) = 704068278961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_2933617829
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (13 : ZMod 704068278961) ^ 352034139480 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 704068278961) ^ 234689426320 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 704068278961) ^ 140813655792 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 704068278961) ^ 240 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1059116674813 : Nat.Prime 1059116674813 := by
  apply lucas_primality 1059116674813 (5 : ZMod 1059116674813)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (12608531843, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (12608531843, 1)] : List FactorBlock).map factorBlockValue).prod) = 1059116674813 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_12608531843
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 1059116674813) ^ 529558337406 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1059116674813) ^ 353038891604 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1059116674813) ^ 151302382116 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1059116674813) ^ 84 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1417279593203 : Nat.Prime 1417279593203 := by
  apply lucas_primality 1417279593203 (2 : ZMod 1417279593203)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (11, 1), (42337, 1), (1521643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (11, 1), (42337, 1), (1521643, 1)] : List FactorBlock).map factorBlockValue).prod) = 1417279593203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_42337
      · exact prime_oneHundredTwentySixDT_1521643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 1417279593203) ^ 708639796601 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417279593203) ^ 128843599382 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417279593203) ^ 33476146 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1417279593203) ^ 931414 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1536136917943 : Nat.Prime 1536136917943 := by
  apply lucas_primality 1536136917943 (3 : ZMod 1536136917943)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (11, 1), (23274801787, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (11, 1), (23274801787, 1)] : List FactorBlock).map factorBlockValue).prod) = 1536136917943 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_23274801787
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1536136917943) ^ 768068458971 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1536136917943) ^ 512045639314 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1536136917943) ^ 139648810722 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1536136917943) ^ 66 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1580387522081 : Nat.Prime 1580387522081 := by
  apply lucas_primality 1580387522081 (3 : ZMod 1580387522081)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (5, 1), (23, 1), (429453131, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (5, 1), (23, 1), (429453131, 1)] : List FactorBlock).map factorBlockValue).prod) = 1580387522081 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_429453131
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1580387522081) ^ 790193761040 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580387522081) ^ 316077504416 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580387522081) ^ 68712500960 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1580387522081) ^ 3680 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1648195396541 : Nat.Prime 1648195396541 := by
  apply lucas_primality 1648195396541 (2 : ZMod 1648195396541)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (7, 1), (11, 1), (2333, 1), (458747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (7, 1), (11, 1), (2333, 1), (458747, 1)] : List FactorBlock).map factorBlockValue).prod) = 1648195396541 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_2333
      · exact prime_oneHundredTwentySixDT_458747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1648195396541) ^ 824097698270 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648195396541) ^ 329639079308 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648195396541) ^ 235456485220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648195396541) ^ 149835945140 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648195396541) ^ 706470380 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1648195396541) ^ 3592820 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1694188519151 : Nat.Prime 1694188519151 := by
  apply lucas_primality 1694188519151 (7 : ZMod 1694188519151)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (33883770383, 1)] : List FactorBlock).map factorBlockValue).prod) = 1694188519151 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_33883770383
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 1694188519151) ^ 847094259575 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 338837703830 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 1694188519151) ^ 50 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2198832051683 : Nat.Prime 2198832051683 := by
  apply lucas_primality 2198832051683 (2 : ZMod 2198832051683)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (37643, 1), (4172341, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (37643, 1), (4172341, 1)] : List FactorBlock).map factorBlockValue).prod) = 2198832051683 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_37643
      · exact prime_oneHundredTwentySixDT_4172341
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 2198832051683) ^ 1099416025841 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2198832051683) ^ 314118864526 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2198832051683) ^ 58412774 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2198832051683) ^ 527002 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2486991238073 : Nat.Prime 2486991238073 := by
  apply lucas_primality 2486991238073 (3 : ZMod 2486991238073)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (19, 1), (859, 1), (1731589, 1)] : List FactorBlock).map factorBlockValue).prod) = 2486991238073 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_859
      · exact prime_oneHundredTwentySixDT_1731589
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2486991238073) ^ 1243495619036 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 226090112552 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 130894275688 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 2895216808 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2486991238073) ^ 1436248 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2731714241063 : Nat.Prime 2731714241063 := by
  apply lucas_primality 2731714241063 (10 : ZMod 2731714241063)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (163, 1), (12553, 1), (29023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (163, 1), (12553, 1), (29023, 1)] : List FactorBlock).map factorBlockValue).prod) = 2731714241063 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_163
      · exact prime_oneHundredTwentySixDT_12553
      · exact prime_oneHundredTwentySixDT_29023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 2731714241063) ^ 1365857120531 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2731714241063) ^ 118770184394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2731714241063) ^ 16758983074 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2731714241063) ^ 217614454 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 2731714241063) ^ 94122394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2781394255853 : Nat.Prime 2781394255853 := by
  apply lucas_primality 2781394255853 (2 : ZMod 2781394255853)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5003, 1), (138986321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5003, 1), (138986321, 1)] : List FactorBlock).map factorBlockValue).prod) = 2781394255853 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5003
      · exact prime_oneHundredTwentySixDT_138986321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2781394255853) ^ 1390697127926 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2781394255853) ^ 555945284 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2781394255853) ^ 20012 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2935169545313 : Nat.Prime 2935169545313 := by
  apply lucas_primality 2935169545313 (3 : ZMod 2935169545313)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (19, 1), (4827581489, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (19, 1), (4827581489, 1)] : List FactorBlock).map factorBlockValue).prod) = 2935169545313 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_4827581489
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 2935169545313) ^ 1467584772656 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2935169545313) ^ 154482607648 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2935169545313) ^ 608 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3662228970263 : Nat.Prime 3662228970263 := by
  apply lucas_primality 3662228970263 (5 : ZMod 3662228970263)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (71, 1), (25790344861, 1)] : List FactorBlock).map factorBlockValue).prod) = 3662228970263 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_71
      · exact prime_oneHundredTwentySixDT_25790344861
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 3662228970263) ^ 1831114485131 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 51580689722 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 3662228970263) ^ 142 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3682577956157 : Nat.Prime 3682577956157 := by
  apply lucas_primality 3682577956157 (3 : ZMod 3682577956157)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (29, 1), (73, 1), (39534697, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (29, 1), (73, 1), (39534697, 1)] : List FactorBlock).map factorBlockValue).prod) = 3682577956157 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_73
      · exact prime_oneHundredTwentySixDT_39534697
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3682577956157) ^ 1841288978078 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3682577956157) ^ 334779814196 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3682577956157) ^ 126985446764 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3682577956157) ^ 50446273372 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3682577956157) ^ 93148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3687111941479 : Nat.Prime 3687111941479 := by
  apply lucas_primality 3687111941479 (3 : ZMod 3687111941479)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (7, 1), (17, 1), (37, 1), (139568171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3687111941479 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_139568171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 3687111941479) ^ 1843555970739 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 1229037313826 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 526730277354 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 216888937734 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 99651674094 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3687111941479) ^ 26418 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4084163851067 : Nat.Prime 4084163851067 := by
  apply lucas_primality 4084163851067 (2 : ZMod 4084163851067)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (13, 1), (104161, 1), (1508081, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (13, 1), (104161, 1), (1508081, 1)] : List FactorBlock).map factorBlockValue).prod) = 4084163851067 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_104161
      · exact prime_oneHundredTwentySixDT_1508081
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4084163851067) ^ 2042081925533 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4084163851067) ^ 314166450082 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4084163851067) ^ 39210106 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4084163851067) ^ 2708186 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4232894525309 : Nat.Prime 4232894525309 := by
  apply lucas_primality 4232894525309 (2 : ZMod 4232894525309)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3793, 1), (278993839, 1)] : List FactorBlock).map factorBlockValue).prod) = 4232894525309 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3793
      · exact prime_oneHundredTwentySixDT_278993839
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 4232894525309) ^ 2116447262654 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 1115975356 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4232894525309) ^ 15172 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4238739538669 : Nat.Prime 4238739538669 := by
  apply lucas_primality 4238739538669 (7 : ZMod 4238739538669)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (39247588321, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (39247588321, 1)] : List FactorBlock).map factorBlockValue).prod) = 4238739538669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_39247588321
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 4238739538669) ^ 2119369769334 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4238739538669) ^ 1412913179556 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 4238739538669) ^ 108 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4254486039403 : Nat.Prime 4254486039403 := by
  apply lucas_primality 4254486039403 (2 : ZMod 4254486039403)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (31, 2), (593, 1), (1244279, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (31, 2), (593, 1), (1244279, 1)] : List FactorBlock).map factorBlockValue).prod) = 4254486039403 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_31
      · exact prime_oneHundredTwentySixDT_593
      · exact prime_oneHundredTwentySixDT_1244279
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4254486039403) ^ 2127243019701 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4254486039403) ^ 1418162013134 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4254486039403) ^ 137241485142 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4254486039403) ^ 7174512714 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4254486039403) ^ 3419238 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4375221181031 : Nat.Prime 4375221181031 := by
  apply lucas_primality 4375221181031 (14 : ZMod 4375221181031)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (7, 1), (31, 1), (2016230959, 1)] : List FactorBlock).map factorBlockValue).prod) = 4375221181031 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_31
      · exact prime_oneHundredTwentySixDT_2016230959
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 4375221181031) ^ 2187610590515 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 875044236206 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 625031597290 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 141136167130 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 4375221181031) ^ 2170 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4421885247991 : Nat.Prime 4421885247991 := by
  apply lucas_primality 4421885247991 (6 : ZMod 4421885247991)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (89, 1), (2081, 1), (37897, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (89, 1), (2081, 1), (37897, 1)] : List FactorBlock).map factorBlockValue).prod) = 4421885247991 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_2081
      · exact prime_oneHundredTwentySixDT_37897
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 4421885247991) ^ 2210942623995 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 1473961749330 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 884377049598 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 631697892570 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 49684103910 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 2124884790 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 4421885247991) ^ 116681670 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6653737764137 : Nat.Prime 6653737764137 := by
  apply lucas_primality 6653737764137 (3 : ZMod 6653737764137)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (31333, 1), (26544449, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (31333, 1), (26544449, 1)] : List FactorBlock).map factorBlockValue).prod) = 6653737764137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_31333
      · exact prime_oneHundredTwentySixDT_26544449
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 6653737764137) ^ 3326868882068 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6653737764137) ^ 212355592 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 6653737764137) ^ 250664 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_8097073720069 : Nat.Prime 8097073720069 := by
  apply lucas_primality 8097073720069 (2 : ZMod 8097073720069)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (674756143339, 1)] : List FactorBlock).map factorBlockValue).prod) = 8097073720069 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_674756143339
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 8097073720069) ^ 4048536860034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 2699024573356 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 8097073720069) ^ 12 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_10839209037929 : Nat.Prime 10839209037929 := by
  apply lucas_primality 10839209037929 (3 : ZMod 10839209037929)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (4703, 1), (288092947, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (4703, 1), (288092947, 1)] : List FactorBlock).map factorBlockValue).prod) = 10839209037929 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_4703
      · exact prime_oneHundredTwentySixDT_288092947
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 10839209037929) ^ 5419604518964 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10839209037929) ^ 2304743576 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10839209037929) ^ 37624 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_11013696930283 : Nat.Prime 11013696930283 := by
  apply lucas_primality 11013696930283 (5 : ZMod 11013696930283)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (347, 1), (23929, 1), (221069, 1)] : List FactorBlock).map factorBlockValue).prod) = 11013696930283 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_347
      · exact prime_oneHundredTwentySixDT_23929
      · exact prime_oneHundredTwentySixDT_221069
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 11013696930283) ^ 5506848465141 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 3671232310094 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 31739760606 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 460265658 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 11013696930283) ^ 49820178 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_12881490443483 : Nat.Prime 12881490443483 := by
  apply lucas_primality 12881490443483 (2 : ZMod 12881490443483)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (9479, 1), (679475179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (9479, 1), (679475179, 1)] : List FactorBlock).map factorBlockValue).prod) = 12881490443483 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_9479
      · exact prime_oneHundredTwentySixDT_679475179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 12881490443483) ^ 6440745221741 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12881490443483) ^ 1358950358 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 12881490443483) ^ 18958 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_13185563172329 : Nat.Prime 13185563172329 := by
  apply lucas_primality 13185563172329 (3 : ZMod 13185563172329)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (1648195396541, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (1648195396541, 1)] : List FactorBlock).map factorBlockValue).prod) = 13185563172329 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1648195396541
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 13185563172329) ^ 6592781586164 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 13185563172329) ^ 8 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_13971226936099 : Nat.Prime 13971226936099 := by
  apply lucas_primality 13971226936099 (2 : ZMod 13971226936099)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (21617, 1), (6336347, 1)] : List FactorBlock).map factorBlockValue).prod) = 13971226936099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_21617
      · exact prime_oneHundredTwentySixDT_6336347
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 13971226936099) ^ 6985613468049 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 4657075645366 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 821836878594 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 646307394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13971226936099) ^ 2204934 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_14305552217941 : Nat.Prime 14305552217941 := by
  apply lucas_primality 14305552217941 (2 : ZMod 14305552217941)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (6427, 1), (37097537, 1)] : List FactorBlock).map factorBlockValue).prod) = 14305552217941 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_6427
      · exact prime_oneHundredTwentySixDT_37097537
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 14305552217941) ^ 7152776108970 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 4768517405980 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2861110443588 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 2225852220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 14305552217941) ^ 385620 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_17160791887493 : Nat.Prime 17160791887493 := by
  apply lucas_primality 17160791887493 (2 : ZMod 17160791887493)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (61, 1), (6393737663, 1)] : List FactorBlock).map factorBlockValue).prod) = 17160791887493 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_61
      · exact prime_oneHundredTwentySixDT_6393737663
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 17160791887493) ^ 8580395943746 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 1560071989772 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 281324457172 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 17160791887493) ^ 2684 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_19690644203179 : Nat.Prime 19690644203179 := by
  apply lucas_primality 19690644203179 (2 : ZMod 19690644203179)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (2551, 1), (98958901, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (2551, 1), (98958901, 1)] : List FactorBlock).map factorBlockValue).prod) = 19690644203179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_2551
      · exact prime_oneHundredTwentySixDT_98958901
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 19690644203179) ^ 9845322101589 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 6563548067726 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 1514664938706 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 7718794278 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 19690644203179) ^ 198978 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_20772473328163 : Nat.Prime 20772473328163 := by
  apply lucas_primality 20772473328163 (2 : ZMod 20772473328163)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (61, 1), (8093, 1), (86579, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (61, 1), (8093, 1), (86579, 1)] : List FactorBlock).map factorBlockValue).prod) = 20772473328163 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_61
      · exact prime_oneHundredTwentySixDT_8093
      · exact prime_oneHundredTwentySixDT_86579
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 20772473328163) ^ 10386236664081 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 20772473328163) ^ 6924157776054 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 20772473328163) ^ 340532349642 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 20772473328163) ^ 2566721034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 20772473328163) ^ 239925078 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_27165561535027 : Nat.Prime 27165561535027 := by
  apply lucas_primality 27165561535027 (2 : ZMod 27165561535027)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (41, 1), (47, 1), (293, 1), (2672987, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (41, 1), (47, 1), (293, 1), (2672987, 1)] : List FactorBlock).map factorBlockValue).prod) = 27165561535027 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_41
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_293
      · exact prime_oneHundredTwentySixDT_2672987
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 27165561535027) ^ 13582780767513 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 27165561535027) ^ 9055187178342 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 27165561535027) ^ 662574671586 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 27165561535027) ^ 577990670958 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 27165561535027) ^ 92715227082 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 27165561535027) ^ 10162998 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_32780570892757 : Nat.Prime 32780570892757 := by
  apply lucas_primality 32780570892757 (5 : ZMod 32780570892757)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (2731714241063, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (2731714241063, 1)] : List FactorBlock).map factorBlockValue).prod) = 32780570892757 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_2731714241063
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 32780570892757) ^ 16390285446378 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 32780570892757) ^ 10926856964252 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 32780570892757) ^ 12 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_34465229850343 : Nat.Prime 34465229850343 := by
  apply lucas_primality 34465229850343 (3 : ZMod 34465229850343)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (376003, 1), (15277019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (376003, 1), (15277019, 1)] : List FactorBlock).map factorBlockValue).prod) = 34465229850343 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_376003
      · exact prime_oneHundredTwentySixDT_15277019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 34465229850343) ^ 17232614925171 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34465229850343) ^ 11488409950114 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34465229850343) ^ 91662114 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34465229850343) ^ 2256018 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_45752552594669 : Nat.Prime 45752552594669 := by
  apply lucas_primality 45752552594669 (2 : ZMod 45752552594669)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (47, 1), (243364641461, 1)] : List FactorBlock).map factorBlockValue).prod) = 45752552594669 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_243364641461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 45752552594669) ^ 22876276297334 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 973458565844 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 45752552594669) ^ 188 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_77288942660899 : Nat.Prime 77288942660899 := by
  apply lucas_primality 77288942660899 (2 : ZMod 77288942660899)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (12881490443483, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (12881490443483, 1)] : List FactorBlock).map factorBlockValue).prod) = 77288942660899 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_12881490443483
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 77288942660899) ^ 38644471330449 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77288942660899) ^ 25762980886966 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 77288942660899) ^ 6 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_81722092943269 : Nat.Prime 81722092943269 := by
  apply lucas_primality 81722092943269 (10 : ZMod 81722092943269)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (226813, 1), (3336167, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (226813, 1), (3336167, 1)] : List FactorBlock).map factorBlockValue).prod) = 81722092943269 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_226813
      · exact prime_oneHundredTwentySixDT_3336167
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (10 : ZMod 81722092943269) ^ 40861046471634 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 81722092943269) ^ 27240697647756 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 81722092943269) ^ 360306036 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 81722092943269) ^ 24495804 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_83089893312653 : Nat.Prime 83089893312653 := by
  apply lucas_primality 83089893312653 (2 : ZMod 83089893312653)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (20772473328163, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (20772473328163, 1)] : List FactorBlock).map factorBlockValue).prod) = 83089893312653 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_20772473328163
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (2 : ZMod 83089893312653) ^ 41544946656326 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 83089893312653) ^ 4 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_95762726757961 : Nat.Prime 95762726757961 := by
  apply lucas_primality 95762726757961 (11 : ZMod 95762726757961)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (113, 1), (7062147991, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (113, 1), (7062147991, 1)] : List FactorBlock).map factorBlockValue).prod) = 95762726757961 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_113
      · exact prime_oneHundredTwentySixDT_7062147991
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 95762726757961) ^ 47881363378980 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 95762726757961) ^ 31920908919320 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 95762726757961) ^ 19152545351592 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 95762726757961) ^ 847457758920 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 95762726757961) ^ 13560 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_104196394828751 : Nat.Prime 104196394828751 := by
  apply lucas_primality 104196394828751 (14 : ZMod 104196394828751)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 4), (7, 1), (53, 1), (224682253, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 4), (7, 1), (53, 1), (224682253, 1)] : List FactorBlock).map factorBlockValue).prod) = 104196394828751 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_53
      · exact prime_oneHundredTwentySixDT_224682253
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 104196394828751) ^ 52098197414375 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 20839278965750 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 14885199261250 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 1965969713750 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 104196394828751) ^ 463750 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_113993486613649 : Nat.Prime 113993486613649 := by
  apply lucas_primality 113993486613649 (7 : ZMod 113993486613649)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (3, 2), (19, 1), (317, 1), (131433079, 1)] : List FactorBlock).map factorBlockValue).prod) = 113993486613649 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_317
      · exact prime_oneHundredTwentySixDT_131433079
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 113993486613649) ^ 56996743306824 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 37997828871216 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 5999657190192 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 359600904144 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 113993486613649) ^ 867312 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_140039214386303 : Nat.Prime 140039214386303 := by
  apply lucas_primality 140039214386303 (10 : ZMod 140039214386303)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (11, 1), (172049, 1), (5285387, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (11, 1), (172049, 1), (5285387, 1)] : List FactorBlock).map factorBlockValue).prod) = 140039214386303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_172049
      · exact prime_oneHundredTwentySixDT_5285387
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 140039214386303) ^ 70019607193151 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 140039214386303) ^ 20005602055186 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 140039214386303) ^ 12730837671482 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 140039214386303) ^ 813949598 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 140039214386303) ^ 26495546 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_148631737990633 : Nat.Prime 148631737990633 := by
  apply lucas_primality 148631737990633 (10 : ZMod 148631737990633)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (13, 1), (47, 1), (691, 1), (14668343, 1)] : List FactorBlock).map factorBlockValue).prod) = 148631737990633 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_691
      · exact prime_oneHundredTwentySixDT_14668343
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (10 : ZMod 148631737990633) ^ 74315868995316 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 49543912663544 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 11433210614664 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 3162377404056 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 215096581752 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (10 : ZMod 148631737990633) ^ 10132824 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_181040488126411 : Nat.Prime 181040488126411 := by
  apply lucas_primality 181040488126411 (3 : ZMod 181040488126411)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (11, 2), (449, 1), (10303, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (11, 2), (449, 1), (10303, 1), (10781, 1)] : List FactorBlock).map factorBlockValue).prod) = 181040488126411 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_449
      · exact prime_oneHundredTwentySixDT_10303
      · exact prime_oneHundredTwentySixDT_10781
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 181040488126411) ^ 90520244063205 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 60346829375470 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 36208097625282 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 16458226193310 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 403208214090 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 17571628470 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 181040488126411) ^ 16792550610 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_204285462728549 : Nat.Prime 204285462728549 := by
  apply lucas_primality 204285462728549 (2 : ZMod 204285462728549)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (46381, 1), (1101126877, 1)] : List FactorBlock).map factorBlockValue).prod) = 204285462728549 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_46381
      · exact prime_oneHundredTwentySixDT_1101126877
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 204285462728549) ^ 102142731364274 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 4404507508 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 204285462728549) ^ 185524 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_207351775701617 : Nat.Prime 207351775701617 := by
  apply lucas_primality 207351775701617 (5 : ZMod 207351775701617)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (13, 1), (271, 1), (525505291, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (13, 1), (271, 1), (525505291, 1)] : List FactorBlock).map factorBlockValue).prod) = 207351775701617 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_271
      · exact prime_oneHundredTwentySixDT_525505291
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 207351775701617) ^ 103675887850808 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 207351775701617) ^ 29621682243088 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 207351775701617) ^ 15950136592432 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 207351775701617) ^ 765135703696 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 207351775701617) ^ 394576 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_233754034370677 : Nat.Prime 233754034370677 := by
  apply lucas_primality 233754034370677 (2 : ZMod 233754034370677)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (53, 1), (2903, 1), (126606197, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (53, 1), (2903, 1), (126606197, 1)] : List FactorBlock).map factorBlockValue).prod) = 233754034370677 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_53
      · exact prime_oneHundredTwentySixDT_2903
      · exact prime_oneHundredTwentySixDT_126606197
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 233754034370677) ^ 116877017185338 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 233754034370677) ^ 77918011456892 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 233754034370677) ^ 4410453478692 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 233754034370677) ^ 80521541292 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 233754034370677) ^ 1846308 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_254952210308099 : Nat.Prime 254952210308099 := by
  apply lucas_primality 254952210308099 (2 : ZMod 254952210308099)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (83, 1), (157, 1), (443, 1), (991, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (83, 1), (157, 1), (443, 1), (991, 1), (22283, 1)] : List FactorBlock).map factorBlockValue).prod) = 254952210308099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_83
      · exact prime_oneHundredTwentySixDT_157
      · exact prime_oneHundredTwentySixDT_443
      · exact prime_oneHundredTwentySixDT_991
      · exact prime_oneHundredTwentySixDT_22283
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 254952210308099) ^ 127476105154049 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 254952210308099) ^ 3071713377206 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 254952210308099) ^ 1623899428714 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 254952210308099) ^ 575512890086 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 254952210308099) ^ 257267618878 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 254952210308099) ^ 11441556806 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_322094651376551 : Nat.Prime 322094651376551 := by
  apply lucas_primality 322094651376551 (11 : ZMod 322094651376551)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (13, 1), (19, 1), (971, 1), (26859463, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (13, 1), (19, 1), (971, 1), (26859463, 1)] : List FactorBlock).map factorBlockValue).prod) = 322094651376551 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_971
      · exact prime_oneHundredTwentySixDT_26859463
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 322094651376551) ^ 161047325688275 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 322094651376551) ^ 64418930275310 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 322094651376551) ^ 24776511644350 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 322094651376551) ^ 16952350072450 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 322094651376551) ^ 331714368050 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 322094651376551) ^ 11991850 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_345887841190189 : Nat.Prime 345887841190189 := by
  apply lucas_primality 345887841190189 (2 : ZMod 345887841190189)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (11, 1), (47, 1), (89, 1), (401, 1), (1562173, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (11, 1), (47, 1), (89, 1), (401, 1), (1562173, 1)] : List FactorBlock).map factorBlockValue).prod) = 345887841190189 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_401
      · exact prime_oneHundredTwentySixDT_1562173
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 345887841190189) ^ 172943920595094 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 115295947063396 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 31444349199108 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 7359315770004 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 3886380238092 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 862563194988 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 345887841190189) ^ 221414556 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_366020420757353 : Nat.Prime 366020420757353 := by
  apply lucas_primality 366020420757353 (3 : ZMod 366020420757353)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (45752552594669, 1)] : List FactorBlock).map factorBlockValue).prod) = 366020420757353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_45752552594669
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · change (3 : ZMod 366020420757353) ^ 183010210378676 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 366020420757353) ^ 8 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_605401060944023 : Nat.Prime 605401060944023 := by
  apply lucas_primality 605401060944023 (5 : ZMod 605401060944023)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (701, 1), (9769, 1), (6314617, 1)] : List FactorBlock).map factorBlockValue).prod) = 605401060944023 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_701
      · exact prime_oneHundredTwentySixDT_9769
      · exact prime_oneHundredTwentySixDT_6314617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 605401060944023) ^ 302700530472011 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 86485865849146 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 863624908622 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 61971651238 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 605401060944023) ^ 95872966 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_621760403722501 : Nat.Prime 621760403722501 := by
  apply lucas_primality 621760403722501 (26 : ZMod 621760403722501)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (5, 4), (7, 1), (59, 1), (66909917, 1)] : List FactorBlock).map factorBlockValue).prod) = 621760403722501 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_59
      · exact prime_oneHundredTwentySixDT_66909917
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (26 : ZMod 621760403722501) ^ 310880201861250 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 207253467907500 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 124352080744500 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 88822914817500 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 10538311927500 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (26 : ZMod 621760403722501) ^ 9292500 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_829722028640579 : Nat.Prime 829722028640579 := by
  apply lucas_primality 829722028640579 (2 : ZMod 829722028640579)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (14305552217941, 1)] : List FactorBlock).map factorBlockValue).prod) = 829722028640579 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_14305552217941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 829722028640579) ^ 414861014320289 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 28611104435882 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 829722028640579) ^ 58 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_910493559186037 : Nat.Prime 910493559186037 := by
  apply lucas_primality 910493559186037 (2 : ZMod 910493559186037)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (7, 1), (10839209037929, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (7, 1), (10839209037929, 1)] : List FactorBlock).map factorBlockValue).prod) = 910493559186037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_10839209037929
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 910493559186037) ^ 455246779593018 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 910493559186037) ^ 303497853062012 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 910493559186037) ^ 130070508455148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 910493559186037) ^ 84 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1447960293405401 : Nat.Prime 1447960293405401 := by
  apply lucas_primality 1447960293405401 (6 : ZMod 1447960293405401)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 2), (17, 1), (425870674531, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 2), (17, 1), (425870674531, 1)] : List FactorBlock).map factorBlockValue).prod) = 1447960293405401 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_425870674531
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (6 : ZMod 1447960293405401) ^ 723980146702700 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1447960293405401) ^ 289592058681080 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1447960293405401) ^ 85174134906200 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 1447960293405401) ^ 3400 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1452722104942727 : Nat.Prime 1452722104942727 := by
  apply lucas_primality 1452722104942727 (5 : ZMod 1452722104942727)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (197, 1), (3687111941479, 1)] : List FactorBlock).map factorBlockValue).prod) = 1452722104942727 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_197
      · exact prime_oneHundredTwentySixDT_3687111941479
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (5 : ZMod 1452722104942727) ^ 726361052471363 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 7374223882958 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 1452722104942727) ^ 394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2161100158678807 : Nat.Prime 2161100158678807 := by
  apply lucas_primality 2161100158678807 (5 : ZMod 2161100158678807)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (239, 1), (2579, 1), (30755359, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (239, 1), (2579, 1), (30755359, 1)] : List FactorBlock).map factorBlockValue).prod) = 2161100158678807 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_239
      · exact prime_oneHundredTwentySixDT_2579
      · exact prime_oneHundredTwentySixDT_30755359
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 2161100158678807) ^ 1080550079339403 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2161100158678807) ^ 720366719559602 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2161100158678807) ^ 113742113614674 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2161100158678807) ^ 9042260078154 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2161100158678807) ^ 837960511314 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 2161100158678807) ^ 70267434 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5429914634945569 : Nat.Prime 5429914634945569 := by
  apply lucas_primality 5429914634945569 (13 : ZMod 5429914634945569)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (3, 1), (379, 1), (439, 1), (3499, 1), (97157, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (3, 1), (379, 1), (439, 1), (3499, 1), (97157, 1)] : List FactorBlock).map factorBlockValue).prod) = 5429914634945569 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_379
      · exact prime_oneHundredTwentySixDT_439
      · exact prime_oneHundredTwentySixDT_3499
      · exact prime_oneHundredTwentySixDT_97157
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (13 : ZMod 5429914634945569) ^ 2714957317472784 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 5429914634945569) ^ 1809971544981856 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 5429914634945569) ^ 14326951543392 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 5429914634945569) ^ 12368826047712 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 5429914634945569) ^ 1551847566432 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (13 : ZMod 5429914634945569) ^ 55888043424 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6102026044398121 : Nat.Prime 6102026044398121 := by
  apply lucas_primality 6102026044398121 (7 : ZMod 6102026044398121)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (5, 1), (53791, 1), (945329461, 1)] : List FactorBlock).map factorBlockValue).prod) = 6102026044398121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_53791
      · exact prime_oneHundredTwentySixDT_945329461
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 6102026044398121) ^ 3051013022199060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 2034008681466040 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 1220405208879624 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 113439535320 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 6102026044398121) ^ 6454920 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6217604037225011 : Nat.Prime 6217604037225011 := by
  apply lucas_primality 6217604037225011 (2 : ZMod 6217604037225011)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (621760403722501, 1)] : List FactorBlock).map factorBlockValue).prod) = 6217604037225011 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_621760403722501
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 6217604037225011) ^ 3108802018612505 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 1243520807445002 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6217604037225011) ^ 10 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_10391732455352099 : Nat.Prime 10391732455352099 := by
  apply lucas_primality 10391732455352099 (2 : ZMod 10391732455352099)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (17, 1), (23, 1), (181, 1), (11789, 1), (6227671, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (17, 1), (23, 1), (181, 1), (11789, 1), (6227671, 1)] : List FactorBlock).map factorBlockValue).prod) = 10391732455352099 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_181
      · exact prime_oneHundredTwentySixDT_11789
      · exact prime_oneHundredTwentySixDT_6227671
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 10391732455352099) ^ 5195866227676049 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 611278379726594 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 451814454580526 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 57412886493658 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 881477008682 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 10391732455352099) ^ 1668638638 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_12452009194005137 : Nat.Prime 12452009194005137 := by
  apply lucas_primality 12452009194005137 (3 : ZMod 12452009194005137)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (7, 1), (197, 1), (743, 1), (759567493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (7, 1), (197, 1), (743, 1), (759567493, 1)] : List FactorBlock).map factorBlockValue).prod) = 12452009194005137 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_197
      · exact prime_oneHundredTwentySixDT_743
      · exact prime_oneHundredTwentySixDT_759567493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 12452009194005137) ^ 6226004597002568 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 1778858456286448 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 63208168497488 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 16759097165552 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 12452009194005137) ^ 16393552 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_15745880390038507 : Nat.Prime 15745880390038507 := by
  apply lucas_primality 15745880390038507 (3 : ZMod 15745880390038507)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (109, 1), (863, 1), (9299447551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (109, 1), (863, 1), (9299447551, 1)] : List FactorBlock).map factorBlockValue).prod) = 15745880390038507 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_109
      · exact prime_oneHundredTwentySixDT_863
      · exact prime_oneHundredTwentySixDT_9299447551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 15745880390038507) ^ 7872940195019253 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 5248626796679502 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 144457618257234 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 18245516095062 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 15745880390038507) ^ 1693206 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_16108128129825647 : Nat.Prime 16108128129825647 := by
  apply lucas_primality 16108128129825647 (5 : ZMod 16108128129825647)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (283, 1), (14543, 1), (1956927067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (283, 1), (14543, 1), (1956927067, 1)] : List FactorBlock).map factorBlockValue).prod) = 16108128129825647 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_283
      · exact prime_oneHundredTwentySixDT_14543
      · exact prime_oneHundredTwentySixDT_1956927067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 16108128129825647) ^ 8054064064912823 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16108128129825647) ^ 56919180670762 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16108128129825647) ^ 1107620719922 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 16108128129825647) ^ 8231338 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_16695774487261171 : Nat.Prime 16695774487261171 := by
  apply lucas_primality 16695774487261171 (3 : ZMod 16695774487261171)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (7, 1), (97, 1), (167, 1), (545326447, 1)] : List FactorBlock).map factorBlockValue).prod) = 16695774487261171 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_97
      · exact prime_oneHundredTwentySixDT_167
      · exact prime_oneHundredTwentySixDT_545326447
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 16695774487261171) ^ 8347887243630585 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 5565258162420390 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 3339154897452234 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 2385110641037310 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 172121386466610 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 99974697528510 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 16695774487261171) ^ 30616110 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_22406438715596939 : Nat.Prime 22406438715596939 := by
  apply lucas_primality 22406438715596939 (2 : ZMod 22406438715596939)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (59, 1), (572777, 1), (331516583, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (59, 1), (572777, 1), (331516583, 1)] : List FactorBlock).map factorBlockValue).prod) = 22406438715596939 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_59
      · exact prime_oneHundredTwentySixDT_572777
      · exact prime_oneHundredTwentySixDT_331516583
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 22406438715596939) ^ 11203219357798469 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22406438715596939) ^ 379770147721982 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22406438715596939) ^ 39118956794 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 22406438715596939) ^ 67587686 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_40468097940064471 : Nat.Prime 40468097940064471 := by
  apply lucas_primality 40468097940064471 (12 : ZMod 40468097940064471)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (5, 1), (13, 1), (4723, 1), (12343, 1), (197773, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (5, 1), (13, 1), (4723, 1), (12343, 1), (197773, 1)] : List FactorBlock).map factorBlockValue).prod) = 40468097940064471 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_4723
      · exact prime_oneHundredTwentySixDT_12343
      · exact prime_oneHundredTwentySixDT_197773
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (12 : ZMod 40468097940064471) ^ 20234048970032235 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 13489365980021490 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 8093619588012894 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 3112930610774190 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 8568303607890 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 3278627395290 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (12 : ZMod 40468097940064471) ^ 204618921390 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_53241274286720537 : Nat.Prime 53241274286720537 := by
  apply lucas_primality 53241274286720537 (3 : ZMod 53241274286720537)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (145829, 1), (45636734023, 1)] : List FactorBlock).map factorBlockValue).prod) = 53241274286720537 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_145829
      · exact prime_oneHundredTwentySixDT_45636734023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 53241274286720537) ^ 26620637143360268 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 365093872184 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 53241274286720537) ^ 1166632 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_58833051765724217 : Nat.Prime 58833051765724217 := by
  apply lucas_primality 58833051765724217 (3 : ZMod 58833051765724217)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (23, 1), (394717, 1), (810060997, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (23, 1), (394717, 1), (810060997, 1)] : List FactorBlock).map factorBlockValue).prod) = 58833051765724217 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_394717
      · exact prime_oneHundredTwentySixDT_810060997
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 58833051765724217) ^ 29416525882862108 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 58833051765724217) ^ 2557958772422792 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 58833051765724217) ^ 149051223448 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 58833051765724217) ^ 72627928 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_90569982157780019 : Nat.Prime 90569982157780019 := by
  apply lucas_primality 90569982157780019 (2 : ZMod 90569982157780019)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (1667, 1), (27165561535027, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (1667, 1), (27165561535027, 1)] : List FactorBlock).map factorBlockValue).prod) = 90569982157780019 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1667
      · exact prime_oneHundredTwentySixDT_27165561535027
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 90569982157780019) ^ 45284991078890009 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 90569982157780019) ^ 54331123070054 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 90569982157780019) ^ 3334 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_160055020023137399 : Nat.Prime 160055020023137399 := by
  apply lucas_primality 160055020023137399 (17 : ZMod 160055020023137399)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (2579, 1), (26171, 1), (10492747, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (2579, 1), (26171, 1), (10492747, 1)] : List FactorBlock).map factorBlockValue).prod) = 160055020023137399 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_113
      · exact prime_oneHundredTwentySixDT_2579
      · exact prime_oneHundredTwentySixDT_26171
      · exact prime_oneHundredTwentySixDT_10492747
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (17 : ZMod 160055020023137399) ^ 80027510011568699 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 160055020023137399) ^ 1416416106399446 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 160055020023137399) ^ 62060884072562 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 160055020023137399) ^ 6115739559938 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (17 : ZMod 160055020023137399) ^ 15253872034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_171634766386409003 : Nat.Prime 171634766386409003 := by
  apply lucas_primality 171634766386409003 (2 : ZMod 171634766386409003)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (37, 1), (9419, 1), (10706337029, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (37, 1), (9419, 1), (10706337029, 1)] : List FactorBlock).map factorBlockValue).prod) = 171634766386409003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_9419
      · exact prime_oneHundredTwentySixDT_10706337029
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 171634766386409003) ^ 85817383193204501 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 171634766386409003) ^ 7462381147235174 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 171634766386409003) ^ 4638777469902946 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 171634766386409003) ^ 18222185623358 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 171634766386409003) ^ 16031138 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_186336486963187577 : Nat.Prime 186336486963187577 := by
  apply lucas_primality 186336486963187577 (3 : ZMod 186336486963187577)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (691, 1), (141937, 1), (237483941, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (691, 1), (141937, 1), (237483941, 1)] : List FactorBlock).map factorBlockValue).prod) = 186336486963187577 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_691
      · exact prime_oneHundredTwentySixDT_141937
      · exact prime_oneHundredTwentySixDT_237483941
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 186336486963187577) ^ 93168243481593788 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 186336486963187577) ^ 269662065069736 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 186336486963187577) ^ 1312811225848 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 186336486963187577) ^ 784627736 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_262660090292765351 : Nat.Prime 262660090292765351 := by
  apply lucas_primality 262660090292765351 (7 : ZMod 262660090292765351)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 2), (8647, 1), (241603, 1), (2514527, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 2), (8647, 1), (241603, 1), (2514527, 1)] : List FactorBlock).map factorBlockValue).prod) = 262660090292765351 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_8647
      · exact prime_oneHundredTwentySixDT_241603
      · exact prime_oneHundredTwentySixDT_2514527
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 262660090292765351) ^ 131330045146382675 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 262660090292765351) ^ 52532018058553070 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 262660090292765351) ^ 30375863339050 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 262660090292765351) ^ 1087155748450 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 262660090292765351) ^ 104457057050 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_335902595973800657 : Nat.Prime 335902595973800657 := by
  apply lucas_primality 335902595973800657 (3 : ZMod 335902595973800657)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 4), (23, 1), (53, 1), (1559, 1), (97453, 1), (113357, 1)] : List FactorBlock).map factorBlockValue).prod) = 335902595973800657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_53
      · exact prime_oneHundredTwentySixDT_1559
      · exact prime_oneHundredTwentySixDT_97453
      · exact prime_oneHundredTwentySixDT_113357
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 335902595973800657) ^ 167951297986900328 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 14604460694513072 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 6337784829694352 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 215460292478384 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 3446816372752 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 335902595973800657) ^ 2963227643408 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_338234065908919183 : Nat.Prime 338234065908919183 := by
  apply lucas_primality 338234065908919183 (5 : ZMod 338234065908919183)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (1429, 1), (162971, 1), (26895587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (1429, 1), (162971, 1), (26895587, 1)] : List FactorBlock).map factorBlockValue).prod) = 338234065908919183 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_1429
      · exact prime_oneHundredTwentySixDT_162971
      · exact prime_oneHundredTwentySixDT_26895587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 338234065908919183) ^ 169117032954459591 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 112744688636306394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 236692838284758 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 2075424866442 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 338234065908919183) ^ 12575820186 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_691305644086294121 : Nat.Prime 691305644086294121 := by
  apply lucas_primality 691305644086294121 (3 : ZMod 691305644086294121)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (13, 1), (3169, 1), (419512127149, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (13, 1), (3169, 1), (419512127149, 1)] : List FactorBlock).map factorBlockValue).prod) = 691305644086294121 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_3169
      · exact prime_oneHundredTwentySixDT_419512127149
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 691305644086294121) ^ 345652822043147060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 691305644086294121) ^ 138261128817258824 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 691305644086294121) ^ 53177357237407240 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 691305644086294121) ^ 218146306117480 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 691305644086294121) ^ 1647880 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_794625521846198267 : Nat.Prime 794625521846198267 := by
  apply lucas_primality 794625521846198267 (5 : ZMod 794625521846198267)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (19, 1), (1321, 1), (282713, 1), (7998937, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (19, 1), (1321, 1), (282713, 1), (7998937, 1)] : List FactorBlock).map factorBlockValue).prod) = 794625521846198267 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_1321
      · exact prime_oneHundredTwentySixDT_282713
      · exact prime_oneHundredTwentySixDT_7998937
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 794625521846198267) ^ 397312760923099133 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 794625521846198267) ^ 113517931692314038 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 794625521846198267) ^ 41822395886642014 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 794625521846198267) ^ 601533324637546 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 794625521846198267) ^ 2810714476682 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 794625521846198267) ^ 99341390218 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1432677009322898849 : Nat.Prime 1432677009322898849 := by
  apply lucas_primality 1432677009322898849 (3 : ZMod 1432677009322898849)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (139, 1), (322094651376551, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (139, 1), (322094651376551, 1)] : List FactorBlock).map factorBlockValue).prod) = 1432677009322898849 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_139
      · exact prime_oneHundredTwentySixDT_322094651376551
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1432677009322898849) ^ 716338504661449424 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1432677009322898849) ^ 10307028844049632 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1432677009322898849) ^ 4448 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2220502305087140441 : Nat.Prime 2220502305087140441 := by
  apply lucas_primality 2220502305087140441 (3 : ZMod 2220502305087140441)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (5, 1), (101, 1), (191, 1), (48017, 1), (59929613, 1)] : List FactorBlock).map factorBlockValue).prod) = 2220502305087140441 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_101
      · exact prime_oneHundredTwentySixDT_191
      · exact prime_oneHundredTwentySixDT_48017
      · exact prime_oneHundredTwentySixDT_59929613
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 2220502305087140441) ^ 1110251152543570220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 444100461017428088 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 21985171337496440 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 11625666518780840 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 46244086575320 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 2220502305087140441) ^ 37051837880 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2240770280323923587 : Nat.Prime 2240770280323923587 := by
  apply lucas_primality 2240770280323923587 (2 : ZMod 2240770280323923587)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (160055020023137399, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (160055020023137399, 1)] : List FactorBlock).map factorBlockValue).prod) = 2240770280323923587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_160055020023137399
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 2240770280323923587) ^ 1120385140161961793 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2240770280323923587) ^ 320110040046274798 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2240770280323923587) ^ 14 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2611902386087080301 : Nat.Prime 2611902386087080301 := by
  apply lucas_primality 2611902386087080301 (2 : ZMod 2611902386087080301)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 2), (37, 1), (10837, 1), (65139758587, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 2), (37, 1), (10837, 1), (65139758587, 1)] : List FactorBlock).map factorBlockValue).prod) = 2611902386087080301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_10837
      · exact prime_oneHundredTwentySixDT_65139758587
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2611902386087080301) ^ 1305951193043540150 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2611902386087080301) ^ 522380477217416060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2611902386087080301) ^ 70591956380731900 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2611902386087080301) ^ 241017106771900 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2611902386087080301) ^ 40096900 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_2655228585118869301 : Nat.Prime 2655228585118869301 := by
  apply lucas_primality 2655228585118869301 (2 : ZMod 2655228585118869301)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 2), (41, 1), (5002103, 1), (43156297, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 2), (41, 1), (5002103, 1), (43156297, 1)] : List FactorBlock).map factorBlockValue).prod) = 2655228585118869301 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_41
      · exact prime_oneHundredTwentySixDT_5002103
      · exact prime_oneHundredTwentySixDT_43156297
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 2655228585118869301) ^ 1327614292559434650 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655228585118869301) ^ 885076195039623100 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655228585118869301) ^ 531045717023773860 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655228585118869301) ^ 64761672807777300 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655228585118869301) ^ 530822453100 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 2655228585118869301) ^ 61525866900 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3289051958699266037 : Nat.Prime 3289051958699266037 := by
  apply lucas_primality 3289051958699266037 (2 : ZMod 3289051958699266037)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (43, 1), (6174811, 1), (134645171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (43, 1), (6174811, 1), (134645171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3289051958699266037 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_43
      · exact prime_oneHundredTwentySixDT_6174811
      · exact prime_oneHundredTwentySixDT_134645171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 3289051958699266037) ^ 1644525979349633018 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289051958699266037) ^ 143002259073881132 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289051958699266037) ^ 76489580434866652 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289051958699266037) ^ 532656296476 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3289051958699266037) ^ 24427552316 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3873419681044591673 : Nat.Prime 3873419681044591673 := by
  apply lucas_primality 3873419681044591673 (3 : ZMod 3873419681044591673)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (29, 1), (16695774487261171, 1)] : List FactorBlock).map factorBlockValue).prod) = 3873419681044591673 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_16695774487261171
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 3873419681044591673) ^ 1936709840522295836 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 133566195898089368 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 3873419681044591673) ^ 232 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4560736673309267053 : Nat.Prime 4560736673309267053 := by
  apply lucas_primality 4560736673309267053 (2 : ZMod 4560736673309267053)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 2), (7, 1), (19, 1), (29, 1), (397, 1), (6871, 1), (12041273, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 2), (7, 1), (19, 1), (29, 1), (397, 1), (6871, 1), (12041273, 1)] : List FactorBlock).map factorBlockValue).prod) = 4560736673309267053 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_397
      · exact prime_oneHundredTwentySixDT_6871
      · exact prime_oneHundredTwentySixDT_12041273
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 4560736673309267053) ^ 2280368336654633526 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 1520245557769755684 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 651533810472752436 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 240038772279435108 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 157266781838250588 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 11488001695993116 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 663766070922612 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4560736673309267053) ^ 378758680524 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6740694599697793753 : Nat.Prime 6740694599697793753 := by
  apply lucas_primality 6740694599697793753 (5 : ZMod 6740694599697793753)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 1), (19, 1), (31, 1), (167, 1), (353, 1), (8088852907, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 1), (19, 1), (31, 1), (167, 1), (353, 1), (8088852907, 1)] : List FactorBlock).map factorBlockValue).prod) = 6740694599697793753 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_31
      · exact prime_oneHundredTwentySixDT_167
      · exact prime_oneHundredTwentySixDT_353
      · exact prime_oneHundredTwentySixDT_8088852907
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 6740694599697793753) ^ 3370347299848896876 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 2246898199899264584 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 354773399984094408 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 217441761280573992 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 40363440716753256 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 19095452123789784 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 6740694599697793753) ^ 833331336 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_13083895150777256237 : Nat.Prime 13083895150777256237 := by
  apply lucas_primality 13083895150777256237 (2 : ZMod 13083895150777256237)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (359, 1), (12941, 1), (704068278961, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (359, 1), (12941, 1), (704068278961, 1)] : List FactorBlock).map factorBlockValue).prod) = 13083895150777256237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_359
      · exact prime_oneHundredTwentySixDT_12941
      · exact prime_oneHundredTwentySixDT_704068278961
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 13083895150777256237) ^ 6541947575388628118 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13083895150777256237) ^ 36445390392137204 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13083895150777256237) ^ 1011042048587996 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 13083895150777256237) ^ 18583276 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_20057478130520583887 : Nat.Prime 20057478130520583887 := by
  apply lucas_primality 20057478130520583887 (7 : ZMod 20057478130520583887)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 1), (1432677009322898849, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 1), (1432677009322898849, 1)] : List FactorBlock).map factorBlockValue).prod) = 20057478130520583887 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_1432677009322898849
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (7 : ZMod 20057478130520583887) ^ 10028739065260291943 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 20057478130520583887) ^ 2865354018645797698 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 20057478130520583887) ^ 14 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_58870400848523288429 : Nat.Prime 58870400848523288429 := by
  apply lucas_primality 58870400848523288429 (2 : ZMod 58870400848523288429)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (1217, 1), (106861, 1), (113168924711, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (1217, 1), (106861, 1), (113168924711, 1)] : List FactorBlock).map factorBlockValue).prod) = 58870400848523288429 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_1217
      · exact prime_oneHundredTwentySixDT_106861
      · exact prime_oneHundredTwentySixDT_113168924711
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 58870400848523288429) ^ 29435200424261644214 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 48373377854168684 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 550906325493148 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 58870400848523288429) ^ 520199348 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_63963851087738943923 : Nat.Prime 63963851087738943923 := by
  apply lucas_primality 63963851087738943923 (2 : ZMod 63963851087738943923)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (7, 2), (67, 1), (7290317, 1), (1336248751, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (7, 2), (67, 1), (7290317, 1), (1336248751, 1)] : List FactorBlock).map factorBlockValue).prod) = 63963851087738943923 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_67
      · exact prime_oneHundredTwentySixDT_7290317
      · exact prime_oneHundredTwentySixDT_1336248751
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 63963851087738943923) ^ 31981925543869471961 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 63963851087738943923) ^ 9137693012534134846 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 63963851087738943923) ^ 954684344593118566 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 63963851087738943923) ^ 8773809299066 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 63963851087738943923) ^ 47868221422 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_76364612785197585103 : Nat.Prime 76364612785197585103 := by
  apply lucas_primality 76364612785197585103 (5 : ZMod 76364612785197585103)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (23, 1), (89, 1), (6217604037225011, 1)] : List FactorBlock).map factorBlockValue).prod) = 76364612785197585103 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_6217604037225011
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 76364612785197585103) ^ 38182306392598792551 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 25454870928399195034 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 3320200555878155874 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 858029357137051518 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 76364612785197585103) ^ 12282 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_94268036096709849533 : Nat.Prime 94268036096709849533 := by
  apply lucas_primality 94268036096709849533 (2 : ZMod 94268036096709849533)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (23, 1), (263, 1), (16339, 1), (14026408709, 1)] : List FactorBlock).map factorBlockValue).prod) = 94268036096709849533 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_263
      · exact prime_oneHundredTwentySixDT_16339
      · exact prime_oneHundredTwentySixDT_14026408709
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 94268036096709849533) ^ 47134018048354924766 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5545178593924108796 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 4098610265074341284 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 358433597325892964 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 5769510747090388 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 94268036096709849533) ^ 6720753548 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_201837073425402545003 : Nat.Prime 201837073425402545003 := by
  apply lucas_primality 201837073425402545003 (2 : ZMod 201837073425402545003)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (103, 1), (977396369, 1), (1002450643, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (103, 1), (977396369, 1), (1002450643, 1)] : List FactorBlock).map factorBlockValue).prod) = 201837073425402545003 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_103
      · exact prime_oneHundredTwentySixDT_977396369
      · exact prime_oneHundredTwentySixDT_1002450643
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 201837073425402545003) ^ 100918536712701272501 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 201837073425402545003) ^ 1959583237139830534 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 201837073425402545003) ^ 206504832458 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 201837073425402545003) ^ 201343652014 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_237411658455564283589 : Nat.Prime 237411658455564283589 := by
  apply lucas_primality 237411658455564283589 (2 : ZMod 237411658455564283589)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (17, 1), (73, 1), (79, 1), (605401060944023, 1)] : List FactorBlock).map factorBlockValue).prod) = 237411658455564283589 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_73
      · exact prime_oneHundredTwentySixDT_79
      · exact prime_oneHundredTwentySixDT_605401060944023
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 237411658455564283589) ^ 118705829227782141794 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 13965391673856722564 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3252214499391291556 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 3005210866526130172 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 237411658455564283589) ^ 392156 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_249764695279771665523 : Nat.Prime 249764695279771665523 := by
  apply lucas_primality 249764695279771665523 (3 : ZMod 249764695279771665523)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (19, 1), (41, 1), (89, 1), (378137, 1), (1587826921, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (19, 1), (41, 1), (89, 1), (378137, 1), (1587826921, 1)] : List FactorBlock).map factorBlockValue).prod) = 249764695279771665523 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_41
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_378137
      · exact prime_oneHundredTwentySixDT_1587826921
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 249764695279771665523) ^ 124882347639885832761 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 83254898426590555174 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 13145510277882719238 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 6091821836091991842 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 2806344890783951298 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 660513769559106 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 249764695279771665523) ^ 157299698082 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_256223811061086791179 : Nat.Prime 256223811061086791179 := by
  apply lucas_primality 256223811061086791179 (2 : ZMod 256223811061086791179)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (17, 1), (6863, 1), (366020420757353, 1)] : List FactorBlock).map factorBlockValue).prod) = 256223811061086791179 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_6863
      · exact prime_oneHundredTwentySixDT_366020420757353
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 256223811061086791179) ^ 128111905530543395589 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 85407937020362263726 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 15071988885946281834 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 37334082917250006 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 256223811061086791179) ^ 700026 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_377942286057032472047 : Nat.Prime 377942286057032472047 := by
  apply lucas_primality 377942286057032472047 (5 : ZMod 377942286057032472047)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (113, 1), (199, 1), (1592737, 1), (5276183617, 1)] : List FactorBlock).map factorBlockValue).prod) = 377942286057032472047 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_113
      · exact prime_oneHundredTwentySixDT_199
      · exact prime_oneHundredTwentySixDT_1592737
      · exact prime_oneHundredTwentySixDT_5276183617
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 377942286057032472047) ^ 188971143028516236023 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 3344622000504712142 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 1899207467623278754 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 237291081990958 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 377942286057032472047) ^ 71631753838 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_575284891189512700303 : Nat.Prime 575284891189512700303 := by
  apply lucas_primality 575284891189512700303 (5 : ZMod 575284891189512700303)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (1709, 1), (12823, 1), (4375221181031, 1)] : List FactorBlock).map factorBlockValue).prod) = 575284891189512700303 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_1709
      · exact prime_oneHundredTwentySixDT_12823
      · exact prime_oneHundredTwentySixDT_4375221181031
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 575284891189512700303) ^ 287642445594756350151 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 191761630396504233434 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 336620767226163078 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 44863517990291874 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 575284891189512700303) ^ 131487042 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1003362068128038751661 : Nat.Prime 1003362068128038751661 := by
  apply lucas_primality 1003362068128038751661 (3 : ZMod 1003362068128038751661)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (11, 1), (4560736673309267053, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (11, 1), (4560736673309267053, 1)] : List FactorBlock).map factorBlockValue).prod) = 1003362068128038751661 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_4560736673309267053
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (3 : ZMod 1003362068128038751661) ^ 501681034064019375830 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003362068128038751661) ^ 200672413625607750332 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003362068128038751661) ^ 91214733466185341060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1003362068128038751661) ^ 220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1146250422224934728417 : Nat.Prime 1146250422224934728417 := by
  apply lucas_primality 1146250422224934728417 (3 : ZMod 1146250422224934728417)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (11, 1), (13, 1), (23, 1), (7573, 1), (1154401, 1), (1245779, 1)] : List FactorBlock).map factorBlockValue).prod) = 1146250422224934728417 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_7573
      · exact prime_oneHundredTwentySixDT_1154401
      · exact prime_oneHundredTwentySixDT_1245779
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1146250422224934728417) ^ 573125211112467364208 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 104204583838630429856 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 88173109401918056032 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 49836974879344988192 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 151360150828592992 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 992939561058016 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1146250422224934728417) ^ 920107356300704 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1205269042013298899237 : Nat.Prime 1205269042013298899237 := by
  apply lucas_primality 1205269042013298899237 (2 : ZMod 1205269042013298899237)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (23, 1), (1549, 1), (47713, 1), (341461, 1), (519119, 1)] : List FactorBlock).map factorBlockValue).prod) = 1205269042013298899237 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_1549
      · exact prime_oneHundredTwentySixDT_47713
      · exact prime_oneHundredTwentySixDT_341461
      · exact prime_oneHundredTwentySixDT_519119
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 1205269042013298899237) ^ 602634521006649449618 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 52403001826665169532 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 778094927058294964 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 25260810303550372 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 3529741440496276 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 1205269042013298899237) ^ 2321758675782044 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3074685732733041494149 : Nat.Prime 3074685732733041494149 := by
  apply lucas_primality 3074685732733041494149 (2 : ZMod 3074685732733041494149)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (256223811061086791179, 1)] : List FactorBlock).map factorBlockValue).prod) = 3074685732733041494149 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_256223811061086791179
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3074685732733041494149) ^ 1537342866366520747074 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 1024895244244347164716 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3074685732733041494149) ^ 12 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_3970959864830274425357 : Nat.Prime 3970959864830274425357 := by
  apply lucas_primality 3970959864830274425357 (2 : ZMod 3970959864830274425357)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (13, 1), (76364612785197585103, 1)] : List FactorBlock).map factorBlockValue).prod) = 3970959864830274425357 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_76364612785197585103
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 3970959864830274425357) ^ 1985479932415137212678 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 305458451140790340412 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 3970959864830274425357) ^ 52 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5708001368280529770587 : Nat.Prime 5708001368280529770587 := by
  apply lucas_primality 5708001368280529770587 (2 : ZMod 5708001368280529770587)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (23, 1), (3931, 1), (5333, 1), (32497, 1), (182141261, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (23, 1), (3931, 1), (5333, 1), (32497, 1), (182141261, 1)] : List FactorBlock).map factorBlockValue).prod) = 5708001368280529770587 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_23
      · exact prime_oneHundredTwentySixDT_3931
      · exact prime_oneHundredTwentySixDT_5333
      · exact prime_oneHundredTwentySixDT_32497
      · exact prime_oneHundredTwentySixDT_182141261
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 5708001368280529770587) ^ 2854000684140264885293 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5708001368280529770587) ^ 248173972533936076982 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5708001368280529770587) ^ 1452048173055337006 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5708001368280529770587) ^ 1070317151374560242 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5708001368280529770587) ^ 175647024903238138 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5708001368280529770587) ^ 31338321349826 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_6641623043142864665387 : Nat.Prime 6641623043142864665387 := by
  apply lucas_primality 6641623043142864665387 (2 : ZMod 6641623043142864665387)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (47, 1), (269, 1), (262660090292765351, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (47, 1), (269, 1), (262660090292765351, 1)] : List FactorBlock).map factorBlockValue).prod) = 6641623043142864665387 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_269
      · exact prime_oneHundredTwentySixDT_262660090292765351
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 6641623043142864665387) ^ 3320811521571432332693 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6641623043142864665387) ^ 141311128577507758838 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6641623043142864665387) ^ 24690048487519942994 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 6641623043142864665387) ^ 25286 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_9680897125634440093519 : Nat.Prime 9680897125634440093519 := by
  apply lucas_primality 9680897125634440093519 (3 : ZMod 9680897125634440093519)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (13, 1), (17, 1), (277, 1), (2131, 1), (5711, 1), (2165692049, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (13, 1), (17, 1), (277, 1), (2131, 1), (5711, 1), (2165692049, 1)] : List FactorBlock).map factorBlockValue).prod) = 9680897125634440093519 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_277
      · exact prime_oneHundredTwentySixDT_2131
      · exact prime_oneHundredTwentySixDT_5711
      · exact prime_oneHundredTwentySixDT_2165692049
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 9680897125634440093519) ^ 4840448562817220046759 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 3226965708544813364506 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 744684394279572314886 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 569464536802025887854 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 34949087096153213334 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 4542889312827048378 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 1695131697712211538 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9680897125634440093519) ^ 4470117129582 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_9803875754057824351433 : Nat.Prime 9803875754057824351433 := by
  apply lucas_primality 9803875754057824351433 (3 : ZMod 9803875754057824351433)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (13, 1), (94268036096709849533, 1)] : List FactorBlock).map factorBlockValue).prod) = 9803875754057824351433 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_94268036096709849533
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 9803875754057824351433) ^ 4901937877028912175716 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 754144288773678796264 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 9803875754057824351433) ^ 104 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_9926209747558596866141 : Nat.Prime 9926209747558596866141 := by
  apply lucas_primality 9926209747558596866141 (2 : ZMod 9926209747558596866141)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (5, 1), (13, 1), (79, 1), (89, 1), (5429914634945569, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (5, 1), (13, 1), (79, 1), (89, 1), (5429914634945569, 1)] : List FactorBlock).map factorBlockValue).prod) = 9926209747558596866141 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_79
      · exact prime_oneHundredTwentySixDT_89
      · exact prime_oneHundredTwentySixDT_5429914634945569
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 9926209747558596866141) ^ 4963104873779298433070 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926209747558596866141) ^ 1985241949511719373228 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926209747558596866141) ^ 763554595966045912780 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926209747558596866141) ^ 125648224652640466660 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926209747558596866141) ^ 111530446601781987260 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 9926209747558596866141) ^ 1828060 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_25421310806269424633581 : Nat.Prime 25421310806269424633581 := by
  apply lucas_primality 25421310806269424633581 (2 : ZMod 25421310806269424633581)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (7, 3), (6271, 1), (944261, 1), (208604521, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (7, 3), (6271, 1), (944261, 1), (208604521, 1)] : List FactorBlock).map factorBlockValue).prod) = 25421310806269424633581 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_6271
      · exact prime_oneHundredTwentySixDT_944261
      · exact prime_oneHundredTwentySixDT_208604521
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 25421310806269424633581) ^ 12710655403134712316790 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 8473770268756474877860 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 5084262161253884926716 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 3631615829467060661940 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 4053788997969928980 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 26921911215510780 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 25421310806269424633581) ^ 121863661843980 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_34826819892562670796919 : Nat.Prime 34826819892562670796919 := by
  apply lucas_primality 34826819892562670796919 (3 : ZMod 34826819892562670796919)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (503, 1), (21247, 1), (181040488126411, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (503, 1), (21247, 1), (181040488126411, 1)] : List FactorBlock).map factorBlockValue).prod) = 34826819892562670796919 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_503
      · exact prime_oneHundredTwentySixDT_21247
      · exact prime_oneHundredTwentySixDT_181040488126411
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 34826819892562670796919) ^ 17413409946281335398459 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 11608939964187556932306 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 69238210521993381306 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 1639140579496525194 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 34826819892562670796919) ^ 192370338 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_39644202306855086398111 : Nat.Prime 39644202306855086398111 := by
  apply lucas_primality 39644202306855086398111 (11 : ZMod 39644202306855086398111)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 1), (5, 1), (101, 1), (13083895150777256237, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 1), (5, 1), (101, 1), (13083895150777256237, 1)] : List FactorBlock).map factorBlockValue).prod) = 39644202306855086398111 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_101
      · exact prime_oneHundredTwentySixDT_13083895150777256237
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 39644202306855086398111) ^ 19822101153427543199055 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 39644202306855086398111) ^ 13214734102285028799370 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 39644202306855086398111) ^ 7928840461371017279622 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 39644202306855086398111) ^ 392516854523317687110 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 39644202306855086398111) ^ 3030 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_46420562446932988723879 : Nat.Prime 46420562446932988723879 := by
  apply lucas_primality 46420562446932988723879 (3 : ZMod 46420562446932988723879)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 4), (7, 1), (37, 1), (4733, 1), (233754034370677, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 4), (7, 1), (37, 1), (4733, 1), (233754034370677, 1)] : List FactorBlock).map factorBlockValue).prod) = 46420562446932988723879 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_37
      · exact prime_oneHundredTwentySixDT_4733
      · exact prime_oneHundredTwentySixDT_233754034370677
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 46420562446932988723879) ^ 23210281223466494361939 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46420562446932988723879) ^ 15473520815644329574626 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46420562446932988723879) ^ 6631508920990426960554 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46420562446932988723879) ^ 1254609795863053749294 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46420562446932988723879) ^ 9807851774124865566 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 46420562446932988723879) ^ 198587214 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_50435018577897128050349 : Nat.Prime 50435018577897128050349 := by
  apply lucas_primality 50435018577897128050349 (2 : ZMod 50435018577897128050349)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (11, 1), (1146250422224934728417, 1)] : List FactorBlock).map factorBlockValue).prod) = 50435018577897128050349 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_1146250422224934728417
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 50435018577897128050349) ^ 25217509288948564025174 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 4585001688899738913668 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 50435018577897128050349) ^ 44 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_90346810080515535878041 : Nat.Prime 90346810080515535878041 := by
  apply lucas_primality 90346810080515535878041 (11 : ZMod 90346810080515535878041)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (3, 3), (5, 1), (3217, 1), (6367, 1), (4084163851067, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (3, 3), (5, 1), (3217, 1), (6367, 1), (4084163851067, 1)] : List FactorBlock).map factorBlockValue).prod) = 90346810080515535878041 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_3217
      · exact prime_oneHundredTwentySixDT_6367
      · exact prime_oneHundredTwentySixDT_4084163851067
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (11 : ZMod 90346810080515535878041) ^ 45173405040257767939020 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 90346810080515535878041) ^ 30115603360171845292680 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 90346810080515535878041) ^ 18069362016103107175608 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 90346810080515535878041) ^ 28084180938923076120 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 90346810080515535878041) ^ 14189855517593142120 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (11 : ZMod 90346810080515535878041) ^ 22121250120 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_170132879765911238517871 : Nat.Prime 170132879765911238517871 := by
  apply lucas_primality 170132879765911238517871 (3 : ZMod 170132879765911238517871)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 5), (5, 1), (17, 1), (2681039, 1), (1536136917943, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 5), (5, 1), (17, 1), (2681039, 1), (1536136917943, 1)] : List FactorBlock).map factorBlockValue).prod) = 170132879765911238517871 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_2681039
      · exact prime_oneHundredTwentySixDT_1536136917943
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 170132879765911238517871) ^ 85066439882955619258935 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 170132879765911238517871) ^ 56710959921970412839290 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 170132879765911238517871) ^ 34026575953182247703574 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 170132879765911238517871) ^ 10007816456818308148110 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 170132879765911238517871) ^ 63457816080225330 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 170132879765911238517871) ^ 110753721090 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_327291962132932346689703 : Nat.Prime 327291962132932346689703 := by
  apply lucas_primality 327291962132932346689703 (5 : ZMod 327291962132932346689703)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (673, 1), (2267, 1), (19135813, 1), (5605209397, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (673, 1), (2267, 1), (19135813, 1), (5605209397, 1)] : List FactorBlock).map factorBlockValue).prod) = 327291962132932346689703 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_673
      · exact prime_oneHundredTwentySixDT_2267
      · exact prime_oneHundredTwentySixDT_19135813
      · exact prime_oneHundredTwentySixDT_5605209397
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 327291962132932346689703) ^ 163645981066466173344851 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 327291962132932346689703) ^ 486317922931548806374 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 327291962132932346689703) ^ 144372281487839588306 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 327291962132932346689703) ^ 17103635060236654 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 327291962132932346689703) ^ 58390675343566 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_421226894041107731343491 : Nat.Prime 421226894041107731343491 := by
  apply lucas_primality 421226894041107731343491 (2 : ZMod 421226894041107731343491)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (47, 1), (66373, 1), (85621, 1), (157705373099, 1)] : List FactorBlock).map factorBlockValue).prod) = 421226894041107731343491 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_47
      · exact prime_oneHundredTwentySixDT_66373
      · exact prime_oneHundredTwentySixDT_85621
      · exact prime_oneHundredTwentySixDT_157705373099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 421226894041107731343491) ^ 210613447020553865671745 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 84245378808221546268698 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 8962274341300164496670 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 6346359122551455130 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 4919668002488965690 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 421226894041107731343491) ^ 2670973637510 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_878899926231809511221431 : Nat.Prime 878899926231809511221431 := by
  apply lucas_primality 878899926231809511221431 (6 : ZMod 878899926231809511221431)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (5, 1), (7, 1), (797, 1), (125287, 1), (13971226936099, 1)] : List FactorBlock).map factorBlockValue).prod) = 878899926231809511221431 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_797
      · exact prime_oneHundredTwentySixDT_125287
      · exact prime_oneHundredTwentySixDT_13971226936099
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (6 : ZMod 878899926231809511221431) ^ 439449963115904755610715 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 292966642077269837073810 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 175779985246361902244286 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 125557132318829930174490 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 1102760258760112310190 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 7015092756884668890 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (6 : ZMod 878899926231809511221431) ^ 62907855570 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1358023095338404691880353 : Nat.Prime 1358023095338404691880353 := by
  apply lucas_primality 1358023095338404691880353 (3 : ZMod 1358023095338404691880353)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (721333, 1), (58833051765724217, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (721333, 1), (58833051765724217, 1)] : List FactorBlock).map factorBlockValue).prod) = 1358023095338404691880353 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_721333
      · exact prime_oneHundredTwentySixDT_58833051765724217
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (3 : ZMod 1358023095338404691880353) ^ 679011547669202345940176 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358023095338404691880353) ^ 1882657656503174944 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1358023095338404691880353) ^ 23082656 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_1682809102787506222932509 : Nat.Prime 1682809102787506222932509 := by
  apply lucas_primality 1682809102787506222932509 (3 : ZMod 1682809102787506222932509)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (7, 1), (29, 1), (223, 1), (1523, 1), (6102026044398121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1682809102787506222932509 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_223
      · exact prime_oneHundredTwentySixDT_1523
      · exact prime_oneHundredTwentySixDT_6102026044398121
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 1682809102787506222932509) ^ 841404551393753111466254 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 240401300398215174704644 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 58027900096120904239052 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 7546229160482090685796 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 1104930468015434158196 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 1682809102787506222932509) ^ 275778748 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4613081487580689516488033 : Nat.Prime 4613081487580689516488033 := by
  apply lucas_primality 4613081487580689516488033 (5 : ZMod 4613081487580689516488033)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 5), (7, 1), (97, 1), (719, 1), (17207, 1), (17160791887493, 1)] : List FactorBlock).map factorBlockValue).prod) = 4613081487580689516488033 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_97
      · exact prime_oneHundredTwentySixDT_719
      · exact prime_oneHundredTwentySixDT_17207
      · exact prime_oneHundredTwentySixDT_17160791887493
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (5 : ZMod 4613081487580689516488033) ^ 2306540743790344758244016 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 659011641082955645212576 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 47557541109079273365856 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 6415968689263824084128 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268093304328511042976 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 4613081487580689516488033) ^ 268815187424 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_4947216213242855629717763 : Nat.Prime 4947216213242855629717763 := by
  apply lucas_primality 4947216213242855629717763 (2 : ZMod 4947216213242855629717763)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (29, 1), (457757, 1), (186336486963187577, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (29, 1), (457757, 1), (186336486963187577, 1)] : List FactorBlock).map factorBlockValue).prod) = 4947216213242855629717763 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_29
      · exact prime_oneHundredTwentySixDT_457757
      · exact prime_oneHundredTwentySixDT_186336486963187577
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 4947216213242855629717763) ^ 2473608106621427814858881 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4947216213242855629717763) ^ 170593662525615711369578 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4947216213242855629717763) ^ 10807516243864879466 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 4947216213242855629717763) ^ 26549906 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_5604425409968232726351827 : Nat.Prime 5604425409968232726351827 := by
  apply lucas_primality 5604425409968232726351827 (2 : ZMod 5604425409968232726351827)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (4871, 1), (575284891189512700303, 1)] : List FactorBlock).map factorBlockValue).prod) = 5604425409968232726351827 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_4871
      · exact prime_oneHundredTwentySixDT_575284891189512700303
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · change (2 : ZMod 5604425409968232726351827) ^ 2802212704984116363175913 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 1150569782379025400606 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 5604425409968232726351827) ^ 9742 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_10954160408629724675816719 : Nat.Prime 10954160408629724675816719 := by
  apply lucas_primality 10954160408629724675816719 (3 : ZMod 10954160408629724675816719)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (17, 1), (16787, 1), (857453, 1), (2486991238073, 1)] : List FactorBlock).map factorBlockValue).prod) = 10954160408629724675816719 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_17
      · exact prime_oneHundredTwentySixDT_16787
      · exact prime_oneHundredTwentySixDT_857453
      · exact prime_oneHundredTwentySixDT_2486991238073
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 10954160408629724675816719) ^ 5477080204314862337908359 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 3651386802876574891938906 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 644362376978219098577454 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 652538298006178869114 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 12775231305540624006 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 10954160408629724675816719) ^ 4404583434366 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_11695503446412469644848203 : Nat.Prime 11695503446412469644848203 := by
  apply lucas_primality 11695503446412469644848203 (7 : ZMod 11695503446412469644848203)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 2), (7, 1), (2551, 1), (34355329, 1), (1059116674813, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 2), (7, 1), (2551, 1), (34355329, 1), (1059116674813, 1)] : List FactorBlock).map factorBlockValue).prod) = 11695503446412469644848203 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_7
      · exact prime_oneHundredTwentySixDT_2551
      · exact prime_oneHundredTwentySixDT_34355329
      · exact prime_oneHundredTwentySixDT_1059116674813
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (7 : ZMod 11695503446412469644848203) ^ 5847751723206234822424101 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 11695503446412469644848203) ^ 3898501148804156548282734 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 11695503446412469644848203) ^ 1670786206630352806406886 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 11695503446412469644848203) ^ 4584674028385915188102 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 11695503446412469644848203) ^ 340427636318443338 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 11695503446412469644848203) ^ 11042695979154 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_30525743319048283989022861 : Nat.Prime 30525743319048283989022861 := by
  apply lucas_primality 30525743319048283989022861 (19 : ZMod 30525743319048283989022861)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 1), (5, 1), (13, 1), (53, 1), (83, 1), (4013, 1), (991741, 1), (2235374311, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 1), (5, 1), (13, 1), (53, 1), (83, 1), (4013, 1), (991741, 1), (2235374311, 1)] : List FactorBlock).map factorBlockValue).prod) = 30525743319048283989022861 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_13
      · exact prime_oneHundredTwentySixDT_53
      · exact prime_oneHundredTwentySixDT_83
      · exact prime_oneHundredTwentySixDT_4013
      · exact prime_oneHundredTwentySixDT_991741
      · exact prime_oneHundredTwentySixDT_2235374311
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change (19 : ZMod 30525743319048283989022861) ^ 15262871659524141994511430 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 10175247773016094663007620 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 6105148663809656797804572 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 2348134101465252614540220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 575957421114118565830620 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 367780039988533542036420 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 7606714009232066780220 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 30779954967121742460 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (19 : ZMod 30525743319048283989022861) ^ 13655763676282260 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_36025544715104141684747657 : Nat.Prime 36025544715104141684747657 := by
  apply lucas_primality 36025544715104141684747657 (3 : ZMod 36025544715104141684747657)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 3), (11, 1), (8753, 1), (10993193, 1), (4254486039403, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 3), (11, 1), (8753, 1), (10993193, 1), (4254486039403, 1)] : List FactorBlock).map factorBlockValue).prod) = 36025544715104141684747657 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_11
      · exact prime_oneHundredTwentySixDT_8753
      · exact prime_oneHundredTwentySixDT_10993193
      · exact prime_oneHundredTwentySixDT_4254486039403
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (3 : ZMod 36025544715104141684747657) ^ 18012772357552070842373828 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36025544715104141684747657) ^ 3275049519554921971340696 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36025544715104141684747657) ^ 4115793980932724972552 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36025544715104141684747657) ^ 3277077434654712392 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (3 : ZMod 36025544715104141684747657) ^ 8467660812952 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_82850738263045398145957487 : Nat.Prime 82850738263045398145957487 := by
  apply lucas_primality 82850738263045398145957487 (5 : ZMod 82850738263045398145957487)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3203, 1), (142799, 1), (90569982157780019, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3203, 1), (142799, 1), (90569982157780019, 1)] : List FactorBlock).map factorBlockValue).prod) = 82850738263045398145957487 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3203
      · exact prime_oneHundredTwentySixDT_142799
      · exact prime_oneHundredTwentySixDT_90569982157780019
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (5 : ZMod 82850738263045398145957487) ^ 41425369131522699072978743 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 82850738263045398145957487) ^ 25866605764297657866362 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 82850738263045398145957487) ^ 580191305702738801714 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (5 : ZMod 82850738263045398145957487) ^ 914770394 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_344031472048396364587601759 : Nat.Prime 344031472048396364587601759 := by
  apply lucas_primality 344031472048396364587601759 (7 : ZMod 344031472048396364587601759)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (25303, 1), (2444182381, 1), (2781394255853, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (25303, 1), (2444182381, 1), (2781394255853, 1)] : List FactorBlock).map factorBlockValue).prod) = 344031472048396364587601759 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_25303
      · exact prime_oneHundredTwentySixDT_2444182381
      · exact prime_oneHundredTwentySixDT_2781394255853
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (7 : ZMod 344031472048396364587601759) ^ 172015736024198182293800879 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 344031472048396364587601759) ^ 13596469669541017451986 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 344031472048396364587601759) ^ 140755237711696918 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (7 : ZMod 344031472048396364587601759) ^ 123690293572886 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_805219607551111491169900333 : Nat.Prime 805219607551111491169900333 := by
  apply lucas_primality 805219607551111491169900333 (2 : ZMod 805219607551111491169900333)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 2), (3, 3), (1103, 1), (167033, 1), (40468097940064471, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 2), (3, 3), (1103, 1), (167033, 1), (40468097940064471, 1)] : List FactorBlock).map factorBlockValue).prod) = 805219607551111491169900333 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_1103
      · exact prime_oneHundredTwentySixDT_167033
      · exact prime_oneHundredTwentySixDT_40468097940064471
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 805219607551111491169900333) ^ 402609803775555745584950166 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 805219607551111491169900333) ^ 268406535850370497056633444 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 805219607551111491169900333) ^ 730026842748061188730644 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 805219607551111491169900333) ^ 4820721699012240043404 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 805219607551111491169900333) ^ 19897639092 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_7840296178787138203496397979 : Nat.Prime 7840296178787138203496397979 := by
  apply lucas_primality 7840296178787138203496397979 (2 : ZMod 7840296178787138203496397979)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (3, 3), (14627, 1), (9926209747558596866141, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (3, 3), (14627, 1), (9926209747558596866141, 1)] : List FactorBlock).map factorBlockValue).prod) = 7840296178787138203496397979 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_14627
      · exact prime_oneHundredTwentySixDT_9926209747558596866141
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 7840296178787138203496397979) ^ 3920148089393569101748198989 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840296178787138203496397979) ^ 2613432059595712734498799326 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840296178787138203496397979) ^ 536015326368164230771614 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 7840296178787138203496397979) ^ 789858 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_21280803913850803695204508801 : Nat.Prime 21280803913850803695204508801 := by
  apply lucas_primality 21280803913850803695204508801 (14 : ZMod 21280803913850803695204508801)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 7), (3, 2), (5, 2), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 21280803913850803695204508801 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_3
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_171401
      · exact prime_oneHundredTwentySixDT_714027719
      · exact prime_oneHundredTwentySixDT_6037638679
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
    · change (14 : ZMod 21280803913850803695204508801) ^ 10640401956925401847602254400 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 7093601304616934565068169600 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 4256160782770160739040901760 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 124157991574441244188800 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 29803890447915235200 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (14 : ZMod 21280803913850803695204508801) ^ 3524689873852387200 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_24827604566159270977738593611 : Nat.Prime 24827604566159270977738593611 := by
  apply lucas_primality 24827604566159270977738593611 (2 : ZMod 24827604566159270977738593611)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 24827604566159270977738593611 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_443
      · exact prime_oneHundredTwentySixDT_5604425409968232726351827
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · change (2 : ZMod 24827604566159270977738593611) ^ 12413802283079635488869296805 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4965520913231854195547718722 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 56044254099682327263518270 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 24827604566159270977738593611) ^ 4430 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem prime_oneHundredTwentySixDT_74482813698477812933215780811 : Nat.Prime 74482813698477812933215780811 := by
  apply lucas_primality 74482813698477812933215780811 (2 : ZMod 74482813698477812933215780811)
  · rw [← oneHundredTwentySixDTFastPow_eq_pow]
    decide
  · intro q hq hqd
    have hdvd : q ∣ ((([(2, 1), (5, 1), (19, 1), (4339, 1), (90346810080515535878041, 1)] : List FactorBlock).map factorBlockValue).prod) := by
      rwa [show ((([(2, 1), (5, 1), (19, 1), (4339, 1), (90346810080515535878041, 1)] : List FactorBlock).map factorBlockValue).prod) = 74482813698477812933215780811 - 1 by norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl
      · exact prime_oneHundredTwentySixDT_2
      · exact prime_oneHundredTwentySixDT_5
      · exact prime_oneHundredTwentySixDT_19
      · exact prime_oneHundredTwentySixDT_4339
      · exact prime_oneHundredTwentySixDT_90346810080515535878041
      ) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl
    · change (2 : ZMod 74482813698477812933215780811) ^ 37241406849238906466607890405 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477812933215780811) ^ 14896562739695562586643156162 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477812933215780811) ^ 3920148089393569101748198990 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477812933215780811) ^ 17165893915297951816827790 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide
    · change (2 : ZMod 74482813698477812933215780811) ^ 824410 ≠ 1
      rw [← oneHundredTwentySixDTFastPow_eq_pow]
      decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561600 : Nat.totient 148965627396955625866431561600 = 34049087556049349416194048000 := by
  rw [← show ((([(2, 7), (3, 2), (5, 2), (7, 1), (171401, 1), (714027719, 1), (6037638679, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561600 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_171401, prime_oneHundredTwentySixDT_714027719, prime_oneHundredTwentySixDT_6037638679]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561601 : Nat.totient 148965627396955625866431561601 = 141125331218168487662935163604 := by
  rw [← show ((([(19, 1), (7840296178787138203496397979, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561601 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_7840296178787138203496397979]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561602 : Nat.totient 148965627396955625866431561602 = 74482813698475617367827251652 := by
  rw [← show ((([(2, 1), (34465229850343, 1), (2161100158678807, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561602 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_34465229850343, prime_oneHundredTwentySixDT_2161100158678807]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561603 : Nat.totient 148965627396955625866431561603 = 99267173363322577369100578080 := by
  rw [← show ((([(3, 1), (2311, 1), (364979, 1), (58870400848523288429, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561603 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_2311, prime_oneHundredTwentySixDT_364979, prime_oneHundredTwentySixDT_58870400848523288429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561604 : Nat.totient 148965627396955625866431561604 = 74482734410073199223041105800 := by
  rw [← show ((([(2, 2), (939391, 1), (39644202306855086398111, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561604 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_939391, prime_oneHundredTwentySixDT_39644202306855086398111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561605 : Nat.totient 148965627396955625866431561605 = 115951623487360054728465647808 := by
  rw [← show ((([(5, 1), (37, 1), (805219607551111491169900333, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561605 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_37, prime_oneHundredTwentySixDT_805219607551111491169900333]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561606 : Nat.totient 148965627396955625866431561606 = 49607136692194906653271322880 := by
  rw [← show ((([(2, 1), (3, 1), (1321, 1), (4733, 1), (3970959864830274425357, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561606 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_1321, prime_oneHundredTwentySixDT_4733, prime_oneHundredTwentySixDT_3970959864830274425357]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561607 : Nat.totient 148965627396955625866431561607 = 127684823483104822171227052800 := by
  rw [← show ((([(7, 1), (21280803913850803695204508801, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561607 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_21280803913850803695204508801]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561608 : Nat.totient 148965627396955625866431561608 = 67710748990399533199188334080 := by
  rw [← show ((([(2, 3), (11, 1), (75253, 1), (1706007343, 1), (13185563172329, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561608 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_75253, prime_oneHundredTwentySixDT_1706007343, prime_oneHundredTwentySixDT_13185563172329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561609 : Nat.totient 148965627396955625866431561609 = 99310417637143095556091572320 := by
  rw [← show ((([(3, 5), (158265131, 1), (3873419681044591673, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561609 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_158265131, prime_oneHundredTwentySixDT_3873419681044591673]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561610 : Nat.totient 148965627396955625866431561610 = 54981650636798121828408176640 := by
  rw [← show ((([(2, 1), (5, 1), (13, 1), (2843, 1), (62873, 1), (66943, 1), (95762726757961, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561610 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_2843, prime_oneHundredTwentySixDT_62873, prime_oneHundredTwentySixDT_66943, prime_oneHundredTwentySixDT_95762726757961]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561611 : Nat.totient 148965627396955625866431561611 = 145258152804442872989014668840 := by
  rw [← show ((([(47, 1), (271, 1), (11695503446412469644848203, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561611 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_47, prime_oneHundredTwentySixDT_271, prime_oneHundredTwentySixDT_11695503446412469644848203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561612 : Nat.totient 148965627396955625866431561612 = 49224398245835902355831685120 := by
  rw [← show ((([(2, 2), (3, 1), (163, 1), (617, 1), (1231, 1), (14737, 1), (22699, 1), (76163, 1), (3935629, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561612 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_163, prime_oneHundredTwentySixDT_617, prime_oneHundredTwentySixDT_1231, prime_oneHundredTwentySixDT_14737, prime_oneHundredTwentySixDT_22699, prime_oneHundredTwentySixDT_76163, prime_oneHundredTwentySixDT_3935629]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561613 : Nat.totient 148965627396955625866431561613 = 142488860929977308859003738000 := by
  rw [← show ((([(23, 1), (2439250031, 1), (2655228585118869301, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561613 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_23, prime_oneHundredTwentySixDT_2439250031, prime_oneHundredTwentySixDT_2655228585118869301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561614 : Nat.totient 148965627396955625866431561614 = 58549843947253601761539047424 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (73, 1), (83, 1), (906208483, 1), (113993486613649, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561614 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_73, prime_oneHundredTwentySixDT_83, prime_oneHundredTwentySixDT_906208483, prime_oneHundredTwentySixDT_113993486613649]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561615 : Nat.totient 148965627396955625866431561615 = 79448257164532662053234544672 := by
  rw [← show ((([(3, 1), (5, 1), (1025839, 1), (9680897125634440093519, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561615 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_1025839, prime_oneHundredTwentySixDT_9680897125634440093519]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561616 : Nat.totient 148965627396955625866431561616 = 74396210291227423556609518080 := by
  rw [← show ((([(2, 4), (1181, 1), (3163, 1), (9775933, 1), (254952210308099, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561616 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_1181, prime_oneHundredTwentySixDT_3163, prime_oneHundredTwentySixDT_9775933, prime_oneHundredTwentySixDT_254952210308099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561617 : Nat.totient 148965627396955625866431561617 = 148965626702866069970534830960 := by
  rw [← show ((([(261786659, 1), (1194185183, 1), (476504362661, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561617 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_261786659, prime_oneHundredTwentySixDT_1194185183, prime_oneHundredTwentySixDT_476504362661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561618 : Nat.totient 148965627396955625866431561618 = 49655209131999093377111847552 := by
  rw [← show ((([(2, 1), (3, 2), (155440836073, 1), (53241274286720537, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561618 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_155440836073, prime_oneHundredTwentySixDT_53241274286720537]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561619 : Nat.totient 148965627396955625866431561619 = 133203241600597700328404793600 := by
  rw [← show ((([(11, 1), (61, 1), (67498297, 1), (3289051958699266037, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561619 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_61, prime_oneHundredTwentySixDT_67498297, prime_oneHundredTwentySixDT_3289051958699266037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561620 : Nat.totient 148965627396955625866431561620 = 56437122546615800828007002880 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (4339, 1), (90346810080515535878041, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561620 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_4339, prime_oneHundredTwentySixDT_90346810080515535878041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561621 : Nat.totient 148965627396955625866431561621 = 85049388061599742781875338240 := by
  rw [← show ((([(3, 1), (7, 2), (1153, 1), (878899926231809511221431, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561621 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_1153, prime_oneHundredTwentySixDT_878899926231809511221431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561622 : Nat.totient 148965627396955625866431561622 = 74482813698477812933215780810 := by
  rw [← show ((([(2, 1), (74482813698477812933215780811, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561622 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_74482813698477812933215780811]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561623 : Nat.totient 148965627396955625866431561623 = 134749739391370676393760276480 := by
  rw [← show ((([(13, 1), (53, 1), (929, 1), (7789, 1), (84404381, 1), (354000961087, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561623 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_53, prime_oneHundredTwentySixDT_929, prime_oneHundredTwentySixDT_7789, prime_oneHundredTwentySixDT_84404381, prime_oneHundredTwentySixDT_354000961087]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561624 : Nat.totient 148965627396955625866431561624 = 49654731421208415316607784960 := by
  rw [← show ((([(2, 3), (3, 1), (103981, 1), (292202129, 1), (204285462728549, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561624 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_103981, prime_oneHundredTwentySixDT_292202129, prime_oneHundredTwentySixDT_204285462728549]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561625 : Nat.totient 148965627396955625866431561625 = 119172476941094972715501558000 := by
  rw [← show ((([(5, 3), (4771391, 1), (249764695279771665523, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561625 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_4771391, prime_oneHundredTwentySixDT_249764695279771665523]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561626 : Nat.totient 148965627396955625866431561626 = 69594620140958134442604288240 := by
  rw [← show ((([(2, 1), (29, 1), (31, 1), (82850738263045398145957487, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561626 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_29, prime_oneHundredTwentySixDT_31, prime_oneHundredTwentySixDT_82850738263045398145957487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561627 : Nat.totient 148965627396955625866431561627 = 97828023550765878700299967536 := by
  rw [← show ((([(3, 2), (67, 1), (653647, 1), (377942286057032472047, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561627 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_67, prime_oneHundredTwentySixDT_653647, prime_oneHundredTwentySixDT_377942286057032472047]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561628 : Nat.totient 148965627396955625866431561628 = 63842411741534934473606570544 := by
  rw [← show ((([(2, 2), (7, 1), (3662228970263, 1), (1452722104942727, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561628 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_3662228970263, prime_oneHundredTwentySixDT_1452722104942727]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561629 : Nat.totient 148965627396955625866431561629 = 145444273510743142500385699200 := by
  rw [← show ((([(43, 1), (2551, 1), (1358023095338404691880353, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561629 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_43, prime_oneHundredTwentySixDT_2551, prime_oneHundredTwentySixDT_1358023095338404691880353]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561630 : Nat.totient 148965627396955625866431561630 = 36096963598702202229061056000 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1), (11, 1), (2269, 1), (24570248051, 1), (8097073720069, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561630 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_2269, prime_oneHundredTwentySixDT_24570248051, prime_oneHundredTwentySixDT_8097073720069]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561631 : Nat.totient 148965627396955625866431561631 = 140073916499317076959210406400 := by
  rw [← show ((([(17, 1), (1087, 1), (3086389, 1), (2611902386087080301, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561631 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_1087, prime_oneHundredTwentySixDT_3086389, prime_oneHundredTwentySixDT_2611902386087080301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561632 : Nat.totient 148965627396955625866431561632 = 73922731378794084969685816320 := by
  rw [← show ((([(2, 5), (149, 1), (1229, 1), (25421310806269424633581, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561632 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_149, prime_oneHundredTwentySixDT_1229, prime_oneHundredTwentySixDT_25421310806269424633581]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561633 : Nat.totient 148965627396955625866431561633 = 99235991886563045966411022336 := by
  rw [← show ((([(3, 1), (2029, 1), (5153, 1), (16139, 1), (1442173, 1), (204046262249, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561633 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_2029, prime_oneHundredTwentySixDT_5153, prime_oneHundredTwentySixDT_16139, prime_oneHundredTwentySixDT_1442173, prime_oneHundredTwentySixDT_204046262249]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561634 : Nat.totient 148965627396955625866431561634 = 72178377670825781241882378240 := by
  rw [← show ((([(2, 1), (41, 1), (227, 1), (439, 1), (25169, 1), (46313749, 1), (15638890609, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561634 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_41, prime_oneHundredTwentySixDT_227, prime_oneHundredTwentySixDT_439, prime_oneHundredTwentySixDT_25169, prime_oneHundredTwentySixDT_46313749, prime_oneHundredTwentySixDT_15638890609]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561635 : Nat.totient 148965627396955625866431561635 = 102146648346037988205906408576 := by
  rw [← show ((([(5, 1), (7, 1), (84389, 1), (50435018577897128050349, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561635 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_84389, prime_oneHundredTwentySixDT_50435018577897128050349]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561636 : Nat.totient 148965627396955625866431561636 = 43842726457966873164702256128 := by
  rw [← show ((([(2, 2), (3, 3), (13, 1), (23, 1), (4613081487580689516488033, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561636 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_23, prime_oneHundredTwentySixDT_4613081487580689516488033]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561637 : Nat.totient 148965627396955625866431561637 = 148213279104555713175143535024 := by
  rw [← show ((([(199, 1), (39239, 1), (13460448439, 1), (1417279593203, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561637 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_199, prime_oneHundredTwentySixDT_39239, prime_oneHundredTwentySixDT_13460448439, prime_oneHundredTwentySixDT_1417279593203]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561638 : Nat.totient 148965627396955625866431561638 = 73617126458636206876221291456 := by
  rw [← show ((([(2, 1), (89, 1), (2557, 1), (327291962132932346689703, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561638 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_89, prime_oneHundredTwentySixDT_2557, prime_oneHundredTwentySixDT_327291962132932346689703]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561639 : Nat.totient 148965627396955625866431561639 = 93484295750357898690220480512 := by
  rw [← show ((([(3, 1), (19, 1), (157, 1), (1057169473, 1), (15745880390038507, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561639 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_157, prime_oneHundredTwentySixDT_1057169473, prime_oneHundredTwentySixDT_15745880390038507]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561640 : Nat.totient 148965627396955625866431561640 = 59570013160848329787080724480 := by
  rw [← show ((([(2, 3), (5, 1), (3733, 1), (296941, 1), (792613, 1), (4238739538669, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561640 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_3733, prime_oneHundredTwentySixDT_296941, prime_oneHundredTwentySixDT_792613, prime_oneHundredTwentySixDT_4238739538669]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561641 : Nat.totient 148965627396955625866431561641 = 134367118008360497938113408000 := by
  rw [← show ((([(11, 1), (239, 1), (367, 1), (1283, 1), (7793, 1), (4513123, 1), (3421534451, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561641 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_239, prime_oneHundredTwentySixDT_367, prime_oneHundredTwentySixDT_1283, prime_oneHundredTwentySixDT_7793, prime_oneHundredTwentySixDT_4513123, prime_oneHundredTwentySixDT_3421534451]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561642 : Nat.totient 148965627396955625866431561642 = 41409965838392050300513076736 := by
  rw [← show ((([(2, 1), (3, 1), (7, 1), (37, 1), (31177, 1), (3074685732733041494149, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561642 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_37, prime_oneHundredTwentySixDT_31177, prime_oneHundredTwentySixDT_3074685732733041494149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561643 : Nat.totient 148965627396955625866431561643 = 147345987000651371071630644096 := by
  rw [← show ((([(103, 1), (863, 1), (65629, 1), (778979, 1), (32780570892757, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561643 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_103, prime_oneHundredTwentySixDT_863, prime_oneHundredTwentySixDT_65629, prime_oneHundredTwentySixDT_778979, prime_oneHundredTwentySixDT_32780570892757]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561644 : Nat.totient 148965627396955625866431561644 = 73744748962940893934344248000 := by
  rw [← show ((([(2, 2), (101, 1), (120671, 1), (10756573307, 1), (284071622563, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561644 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_101, prime_oneHundredTwentySixDT_120671, prime_oneHundredTwentySixDT_10756573307, prime_oneHundredTwentySixDT_284071622563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561645 : Nat.totient 148965627396955625866431561645 = 77296579961209055840103100416 := by
  rw [← show ((([(3, 2), (5, 1), (59, 2), (97, 1), (9803875754057824351433, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561645 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_59, prime_oneHundredTwentySixDT_97, prime_oneHundredTwentySixDT_9803875754057824351433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561646 : Nat.totient 148965627396955625866431561646 = 74297071020346263756351520000 := by
  rw [← show ((([(2, 1), (401, 1), (128278847423, 1), (1447960293405401, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561646 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_401, prime_oneHundredTwentySixDT_128278847423, prime_oneHundredTwentySixDT_1447960293405401]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561647 : Nat.totient 148965627396955625866431561647 = 148621595924907229501843959456 := by
  rw [← show ((([(433, 1), (344031472048396364587601759, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561647 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_433, prime_oneHundredTwentySixDT_344031472048396364587601759]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561648 : Nat.totient 148965627396955625866431561648 = 46734313015628176964514578432 := by
  rw [← show ((([(2, 4), (3, 1), (17, 2), (31969337, 1), (335902595973800657, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561648 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_31969337, prime_oneHundredTwentySixDT_335902595973800657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561649 : Nat.totient 148965627396955625866431561649 = 117862913984392956763664512128 := by
  rw [← show ((([(7, 1), (13, 1), (11013696930283, 1), (148631737990633, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561649 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_11013696930283, prime_oneHundredTwentySixDT_148631737990633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561650 : Nat.totient 148965627396955625866431561650 = 59529307364414261479988064000 := by
  rw [← show ((([(2, 1), (5, 2), (1051, 1), (239333, 1), (1468819613, 1), (8063847427, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561650 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_1051, prime_oneHundredTwentySixDT_239333, prime_oneHundredTwentySixDT_1468819613, prime_oneHundredTwentySixDT_8063847427]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561651 : Nat.totient 148965627396955625866431561651 = 99048385498747412719371901248 := by
  rw [← show ((([(3, 1), (379, 1), (6653737764137, 1), (19690644203179, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561651 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_379, prime_oneHundredTwentySixDT_6653737764137, prime_oneHundredTwentySixDT_19690644203179]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561652 : Nat.totient 148965627396955625866431561652 = 67711618351869073527997708800 := by
  rw [← show ((([(2, 2), (11, 2), (2282047, 1), (85339979, 1), (1580387522081, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561652 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_2282047, prime_oneHundredTwentySixDT_85339979, prime_oneHundredTwentySixDT_1580387522081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561653 : Nat.totient 148965627396955625866431561653 = 148931106725001680693032232880 := by
  rw [← show ((([(5059, 1), (29347, 1), (1003362068128038751661, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561653 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5059, prime_oneHundredTwentySixDT_29347, prime_oneHundredTwentySixDT_1003362068128038751661]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561654 : Nat.totient 148965627396955625866431561654 = 49655207707848591221882333328 := by
  rw [← show ((([(2, 1), (3, 2), (34858727, 1), (237411658455564283589, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561654 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_34858727, prime_oneHundredTwentySixDT_237411658455564283589]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561655 : Nat.totient 148965627396955625866431561655 = 115063097733202710895773777024 := by
  rw [← show ((([(5, 1), (29, 1), (15263719, 1), (7467106019, 1), (9013747499, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561655 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_29, prime_oneHundredTwentySixDT_15263719, prime_oneHundredTwentySixDT_7467106019, prime_oneHundredTwentySixDT_9013747499]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561656 : Nat.totient 148965627396955625866431561656 = 63806528289284581026551241600 := by
  rw [← show ((([(2, 3), (7, 1), (2411, 1), (7039, 1), (188911, 1), (829722028640579, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561656 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_2411, prime_oneHundredTwentySixDT_7039, prime_oneHundredTwentySixDT_188911, prime_oneHundredTwentySixDT_829722028640579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561657 : Nat.totient 148965627396955625866431561657 = 94927838755452748906291200000 := by
  rw [← show ((([(3, 1), (31, 1), (277, 1), (293, 1), (463, 1), (577, 1), (709, 1), (104196394828751, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561657 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_31, prime_oneHundredTwentySixDT_277, prime_oneHundredTwentySixDT_293, prime_oneHundredTwentySixDT_463, prime_oneHundredTwentySixDT_577, prime_oneHundredTwentySixDT_709, prime_oneHundredTwentySixDT_104196394828751]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561658 : Nat.totient 148965627396955625866431561658 = 69061042037644855609460829120 := by
  rw [← show ((([(2, 1), (19, 1), (47, 1), (381631, 1), (631867, 1), (345887841190189, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561658 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_47, prime_oneHundredTwentySixDT_381631, prime_oneHundredTwentySixDT_631867, prime_oneHundredTwentySixDT_345887841190189]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561659 : Nat.totient 148965627396955625866431561659 = 142327491515125844043341133216 := by
  rw [← show ((([(23, 1), (883, 1), (327359309, 1), (22406438715596939, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561659 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_23, prime_oneHundredTwentySixDT_883, prime_oneHundredTwentySixDT_327359309, prime_oneHundredTwentySixDT_22406438715596939]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561660 : Nat.totient 148965627396955625866431561660 = 39634496499295341840760113472 := by
  rw [← show ((([(2, 2), (3, 1), (5, 1), (443, 1), (5604425409968232726351827, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561660 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_443, prime_oneHundredTwentySixDT_5604425409968232726351827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561661 : Nat.totient 148965627396955625866431561661 = 148965627195118552440290967772 := by
  rw [← show ((([(738048887, 1), (201837073425402545003, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561661 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_738048887, prime_oneHundredTwentySixDT_201837073425402545003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561662 : Nat.totient 148965627396955625866431561662 = 67784961824916718680130156800 := by
  rw [← show ((([(2, 1), (13, 1), (71, 2), (1430321, 1), (794625521846198267, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561662 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_71, prime_oneHundredTwentySixDT_1430321, prime_oneHundredTwentySixDT_794625521846198267]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561663 : Nat.totient 148965627396955625866431561663 = 77215775579529726775957632000 := by
  rw [← show ((([(3, 3), (7, 1), (11, 1), (461, 1), (69997, 1), (2220502305087140441, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561663 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_461, prime_oneHundredTwentySixDT_69997, prime_oneHundredTwentySixDT_2220502305087140441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561664 : Nat.totient 148965627396955625866431561664 = 74477369446325303773582771200 := by
  rw [← show ((([(2, 6), (13681, 1), (170132879765911238517871, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561664 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_13681, prime_oneHundredTwentySixDT_170132879765911238517871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561665 : Nat.totient 148965627396955625866431561665 = 112162350652256589858855472896 := by
  rw [← show ((([(5, 1), (17, 1), (27398863, 1), (63963851087738943923, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561665 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_27398863, prime_oneHundredTwentySixDT_63963851087738943923]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561666 : Nat.totient 148965627396955625866431561666 = 49655209132318541955477187220 := by
  rw [← show ((([(2, 1), (3, 1), (24827604566159270977738593611, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561666 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_24827604566159270977738593611]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561667 : Nat.totient 148965627396955625866431561667 = 147789034215525607711923059328 := by
  rw [← show ((([(173, 1), (587, 1), (2339, 1), (170301979, 1), (3682577956157, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561667 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_173, prime_oneHundredTwentySixDT_587, prime_oneHundredTwentySixDT_2339, prime_oneHundredTwentySixDT_170301979, prime_oneHundredTwentySixDT_3682577956157]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561668 : Nat.totient 148965627396955625866431561668 = 74482649108234094507869389664 := by
  rw [← show ((([(2, 2), (501827, 1), (4607093, 1), (16108128129825647, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561668 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_501827, prime_oneHundredTwentySixDT_4607093, prime_oneHundredTwentySixDT_16108128129825647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561669 : Nat.totient 148965627396955625866431561669 = 99178420695171318852542357760 := by
  rw [← show ((([(3, 1), (881, 1), (5147, 1), (44985986047, 1), (243420692987, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561669 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_881, prime_oneHundredTwentySixDT_5147, prime_oneHundredTwentySixDT_44985986047, prime_oneHundredTwentySixDT_243420692987]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561670 : Nat.totient 148965627396955625866431561670 = 51071482797880299202307827968 := by
  rw [← show ((([(2, 1), (5, 1), (7, 2), (28403, 1), (79847, 1), (5816549, 1), (23046330287, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561670 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_28403, prime_oneHundredTwentySixDT_79847, prime_oneHundredTwentySixDT_5816549, prime_oneHundredTwentySixDT_23046330287]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561671 : Nat.totient 148965627396955625866431561671 = 148954508068651264542419149248 := by
  rw [← show ((([(13397, 1), (143866986457, 1), (77288942660899, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561671 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_13397, prime_oneHundredTwentySixDT_143866986457, prime_oneHundredTwentySixDT_77288942660899]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561672 : Nat.totient 148965627396955625866431561672 = 48500424017800441163614126080 := by
  rw [← show ((([(2, 3), (3, 2), (43, 1), (4282273, 1), (32701811, 1), (343588771969, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561672 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_43, prime_oneHundredTwentySixDT_4282273, prime_oneHundredTwentySixDT_32701811, prime_oneHundredTwentySixDT_343588771969]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561673 : Nat.totient 148965627396955625866431561673 = 146309934255186157848436262400 := by
  rw [← show ((([(79, 1), (191, 1), (47612156521, 1), (207351775701617, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561673 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_79, prime_oneHundredTwentySixDT_191, prime_oneHundredTwentySixDT_47612156521, prime_oneHundredTwentySixDT_207351775701617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561674 : Nat.totient 148965627396955625866431561674 = 67704043749444583643929536000 := by
  rw [← show ((([(2, 1), (11, 1), (9157, 1), (323093, 1), (68264617, 1), (33526403551, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561674 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_9157, prime_oneHundredTwentySixDT_323093, prime_oneHundredTwentySixDT_68264617, prime_oneHundredTwentySixDT_33526403551]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561675 : Nat.totient 148965627396955625866431561675 = 70879543845343547605887513600 := by
  rw [← show ((([(3, 1), (5, 2), (13, 1), (41, 1), (107, 1), (34826819892562670796919, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561675 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_41, prime_oneHundredTwentySixDT_107, prime_oneHundredTwentySixDT_34826819892562670796919]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561676 : Nat.totient 148965627396955625866431561676 = 73072649852464882601760210432 := by
  rw [← show ((([(2, 2), (53, 1), (15137, 1), (46420562446932988723879, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561676 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_53, prime_oneHundredTwentySixDT_15137, prime_oneHundredTwentySixDT_46420562446932988723879]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561677 : Nat.totient 148965627396955625866431561677 = 120919077111016549790387613360 := by
  rw [← show ((([(7, 1), (19, 1), (2659, 1), (421226894041107731343491, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561677 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_2659, prime_oneHundredTwentySixDT_421226894041107731343491]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561678 : Nat.totient 148965627396955625866431561678 = 49655037373740815241650801376 := by
  rw [← show ((([(2, 1), (3, 1), (289103, 1), (20288258719, 1), (4232894525309, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561678 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_289103, prime_oneHundredTwentySixDT_20288258719, prime_oneHundredTwentySixDT_4232894525309]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561679 : Nat.totient 148965627396955625866431561679 = 144939529359167131454582435040 := by
  rw [← show ((([(37, 1), (4421885247991, 1), (910493559186037, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561679 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_37, prime_oneHundredTwentySixDT_4421885247991, prime_oneHundredTwentySixDT_910493559186037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561680 : Nat.totient 148965627396955625866431561680 = 58609427172572705258923891200 := by
  rw [← show ((([(2, 4), (5, 1), (61, 1), (30525743319048283989022861, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561680 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_61, prime_oneHundredTwentySixDT_30525743319048283989022861]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561681 : Nat.totient 148965627396955625866431561681 = 99244693302185305562899465080 := by
  rw [← show ((([(3, 2), (1511, 1), (10954160408629724675816719, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561681 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_1511, prime_oneHundredTwentySixDT_10954160408629724675816719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561682 : Nat.totient 148965627396955625866431561682 = 67007369662518795082863171200 := by
  rw [← show ((([(2, 1), (17, 1), (23, 2), (1451, 1), (5708001368280529770587, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561682 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_23, prime_oneHundredTwentySixDT_1451, prime_oneHundredTwentySixDT_5708001368280529770587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561683 : Nat.totient 148965627396955625866431561683 = 148785934239591862349140770528 := by
  rw [← show ((([(829, 1), (2198832051683, 1), (81722092943269, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561683 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_829, prime_oneHundredTwentySixDT_2198832051683, prime_oneHundredTwentySixDT_81722092943269]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561684 : Nat.totient 148965627396955625866431561684 = 40639589391783839901740040192 := by
  rw [← show ((([(2, 2), (3, 1), (7, 1), (29, 1), (113, 1), (449, 1), (1205269042013298899237, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561684 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_29, prime_oneHundredTwentySixDT_113, prime_oneHundredTwentySixDT_449, prime_oneHundredTwentySixDT_1205269042013298899237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561685 : Nat.totient 148965627396955625866431561685 = 108265477573597322809522944000 := by
  rw [← show ((([(5, 1), (11, 1), (1489, 1), (269851, 1), (6740694599697793753, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561685 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_1489, prime_oneHundredTwentySixDT_269851, prime_oneHundredTwentySixDT_6740694599697793753]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561686 : Nat.totient 148965627396955625866431561686 = 73874569337978020205640904000 := by
  rw [← show ((([(2, 1), (131, 1), (1871, 1), (439583, 1), (691305644086294121, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561686 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_131, prime_oneHundredTwentySixDT_1871, prime_oneHundredTwentySixDT_439583, prime_oneHundredTwentySixDT_691305644086294121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561687 : Nat.totient 148965627396955625866431561687 = 97881172757820266929061713920 := by
  rw [← show ((([(3, 1), (73, 1), (1721, 1), (8423, 1), (335077, 1), (140039214386303, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561687 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_73, prime_oneHundredTwentySixDT_1721, prime_oneHundredTwentySixDT_8423, prime_oneHundredTwentySixDT_335077, prime_oneHundredTwentySixDT_140039214386303]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561688 : Nat.totient 148965627396955625866431561688 = 65402110711422090381491896320 := by
  rw [← show ((([(2, 3), (13, 1), (31, 1), (109, 1), (127, 1), (31039, 1), (36637, 1), (2935169545313, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561688 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_31, prime_oneHundredTwentySixDT_109, prime_oneHundredTwentySixDT_127, prime_oneHundredTwentySixDT_31039, prime_oneHundredTwentySixDT_36637, prime_oneHundredTwentySixDT_2935169545313]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561689 : Nat.totient 148965627396955625866431561689 = 148961398337864239985454013200 := by
  rw [← show ((([(44701, 1), (166147, 1), (20057478130520583887, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561689 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_44701, prime_oneHundredTwentySixDT_166147, prime_oneHundredTwentySixDT_20057478130520583887]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561690 : Nat.totient 148965627396955625866431561690 = 39723899194626241124747289600 := by
  rw [← show ((([(2, 1), (3, 4), (5, 1), (148193, 1), (732506743, 1), (1694188519151, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561690 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_148193, prime_oneHundredTwentySixDT_732506743, prime_oneHundredTwentySixDT_1694188519151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561691 : Nat.totient 148965627396955625866431561691 = 126971500435787976996705704928 := by
  rw [← show ((([(7, 1), (179, 1), (11440553653, 1), (10391732455352099, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561691 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_179, prime_oneHundredTwentySixDT_11440553653, prime_oneHundredTwentySixDT_10391732455352099]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561692 : Nat.totient 148965627396955625866431561692 = 73624304069864586217660723200 := by
  rw [← show ((([(2, 2), (211, 1), (241, 1), (373, 1), (23630317, 1), (83089893312653, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561692 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_211, prime_oneHundredTwentySixDT_241, prime_oneHundredTwentySixDT_373, prime_oneHundredTwentySixDT_23630317, prime_oneHundredTwentySixDT_83089893312653]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561693 : Nat.totient 148965627396955625866431561693 = 99300523832210598199694918864 := by
  rw [← show ((([(3, 1), (10037, 1), (4947216213242855629717763, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561693 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_10037, prime_oneHundredTwentySixDT_4947216213242855629717763]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561694 : Nat.totient 148965627396955625866431561694 = 73370567590184089438240832640 := by
  rw [← show ((([(2, 1), (67, 1), (147503, 1), (1182283, 1), (29290621, 1), (217635829, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561694 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_67, prime_oneHundredTwentySixDT_147503, prime_oneHundredTwentySixDT_1182283, prime_oneHundredTwentySixDT_29290621, prime_oneHundredTwentySixDT_217635829]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561695 : Nat.totient 148965627396955625866431561695 = 119028399738704084126406255424 := by
  rw [← show ((([(5, 1), (827, 1), (36025544715104141684747657, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561695 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_827, prime_oneHundredTwentySixDT_36025544715104141684747657]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561696 : Nat.totient 148965627396955625866431561696 = 42765251812569904718105026560 := by
  rw [← show ((([(2, 5), (3, 1), (11, 1), (19, 1), (596250997, 1), (12452009194005137, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561696 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_11, prime_oneHundredTwentySixDT_19, prime_oneHundredTwentySixDT_596250997, prime_oneHundredTwentySixDT_12452009194005137]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561697 : Nat.totient 148965627396955625866431561697 = 146821209138467423289103429440 := by
  rw [← show ((([(83, 1), (421, 1), (1902517, 1), (2240770280323923587, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561697 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_83, prime_oneHundredTwentySixDT_421, prime_oneHundredTwentySixDT_1902517, prime_oneHundredTwentySixDT_2240770280323923587]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561698 : Nat.totient 148965627396955625866431561698 = 63832314886935686048275893456 := by
  rw [← show ((([(2, 1), (7, 1), (6323, 1), (1682809102787506222932509, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561698 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_7, prime_oneHundredTwentySixDT_6323, prime_oneHundredTwentySixDT_1682809102787506222932509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561699 : Nat.totient 148965627396955625866431561699 = 93338607548032528100950533888 := by
  rw [← show ((([(3, 2), (17, 1), (719, 1), (4003579, 1), (338234065908919183, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561699 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_3, prime_oneHundredTwentySixDT_17, prime_oneHundredTwentySixDT_719, prime_oneHundredTwentySixDT_4003579, prime_oneHundredTwentySixDT_338234065908919183]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561700 : Nat.totient 148965627396955625866431561700 = 59585985293860524631977037600 := by
  rw [← show ((([(2, 2), (5, 2), (224291, 1), (6641623043142864665387, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561700 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_2, prime_oneHundredTwentySixDT_5, prime_oneHundredTwentySixDT_224291, prime_oneHundredTwentySixDT_6641623043142864665387]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_oneHundredTwentySixDT_148965627396955625866431561701 : Nat.totient 148965627396955625866431561701 = 136762230509746879008902676480 := by
  rw [← show ((([(13, 1), (193, 1), (4523, 1), (76481, 1), (171634766386409003, 1)] : List FactorBlock).map factorBlockValue).prod) = 148965627396955625866431561701 by norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_oneHundredTwentySixDT_13, prime_oneHundredTwentySixDT_193, prime_oneHundredTwentySixDT_4523, prime_oneHundredTwentySixDT_76481, prime_oneHundredTwentySixDT_171634766386409003]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

theorem freeKill_64OneHundredTwentySixDT : certifiedKill 1 148965627396955625866431561599 101 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_oneHundredTwentySixDT_148965627396955625866431561600, phi_oneHundredTwentySixDT_148965627396955625866431561601, phi_oneHundredTwentySixDT_148965627396955625866431561602,
    phi_oneHundredTwentySixDT_148965627396955625866431561603, phi_oneHundredTwentySixDT_148965627396955625866431561604, phi_oneHundredTwentySixDT_148965627396955625866431561605,
    phi_oneHundredTwentySixDT_148965627396955625866431561606, phi_oneHundredTwentySixDT_148965627396955625866431561607, phi_oneHundredTwentySixDT_148965627396955625866431561608,
    phi_oneHundredTwentySixDT_148965627396955625866431561609, phi_oneHundredTwentySixDT_148965627396955625866431561610, phi_oneHundredTwentySixDT_148965627396955625866431561611,
    phi_oneHundredTwentySixDT_148965627396955625866431561612, phi_oneHundredTwentySixDT_148965627396955625866431561613, phi_oneHundredTwentySixDT_148965627396955625866431561614,
    phi_oneHundredTwentySixDT_148965627396955625866431561615, phi_oneHundredTwentySixDT_148965627396955625866431561616, phi_oneHundredTwentySixDT_148965627396955625866431561617,
    phi_oneHundredTwentySixDT_148965627396955625866431561618, phi_oneHundredTwentySixDT_148965627396955625866431561619, phi_oneHundredTwentySixDT_148965627396955625866431561620,
    phi_oneHundredTwentySixDT_148965627396955625866431561621, phi_oneHundredTwentySixDT_148965627396955625866431561622, phi_oneHundredTwentySixDT_148965627396955625866431561623,
    phi_oneHundredTwentySixDT_148965627396955625866431561624, phi_oneHundredTwentySixDT_148965627396955625866431561625, phi_oneHundredTwentySixDT_148965627396955625866431561626,
    phi_oneHundredTwentySixDT_148965627396955625866431561627, phi_oneHundredTwentySixDT_148965627396955625866431561628, phi_oneHundredTwentySixDT_148965627396955625866431561629,
    phi_oneHundredTwentySixDT_148965627396955625866431561630, phi_oneHundredTwentySixDT_148965627396955625866431561631, phi_oneHundredTwentySixDT_148965627396955625866431561632,
    phi_oneHundredTwentySixDT_148965627396955625866431561633, phi_oneHundredTwentySixDT_148965627396955625866431561634, phi_oneHundredTwentySixDT_148965627396955625866431561635,
    phi_oneHundredTwentySixDT_148965627396955625866431561636, phi_oneHundredTwentySixDT_148965627396955625866431561637, phi_oneHundredTwentySixDT_148965627396955625866431561638,
    phi_oneHundredTwentySixDT_148965627396955625866431561639, phi_oneHundredTwentySixDT_148965627396955625866431561640, phi_oneHundredTwentySixDT_148965627396955625866431561641,
    phi_oneHundredTwentySixDT_148965627396955625866431561642, phi_oneHundredTwentySixDT_148965627396955625866431561643, phi_oneHundredTwentySixDT_148965627396955625866431561644,
    phi_oneHundredTwentySixDT_148965627396955625866431561645, phi_oneHundredTwentySixDT_148965627396955625866431561646, phi_oneHundredTwentySixDT_148965627396955625866431561647,
    phi_oneHundredTwentySixDT_148965627396955625866431561648, phi_oneHundredTwentySixDT_148965627396955625866431561649, phi_oneHundredTwentySixDT_148965627396955625866431561650,
    phi_oneHundredTwentySixDT_148965627396955625866431561651, phi_oneHundredTwentySixDT_148965627396955625866431561652, phi_oneHundredTwentySixDT_148965627396955625866431561653,
    phi_oneHundredTwentySixDT_148965627396955625866431561654, phi_oneHundredTwentySixDT_148965627396955625866431561655, phi_oneHundredTwentySixDT_148965627396955625866431561656,
    phi_oneHundredTwentySixDT_148965627396955625866431561657, phi_oneHundredTwentySixDT_148965627396955625866431561658, phi_oneHundredTwentySixDT_148965627396955625866431561659,
    phi_oneHundredTwentySixDT_148965627396955625866431561660, phi_oneHundredTwentySixDT_148965627396955625866431561661, phi_oneHundredTwentySixDT_148965627396955625866431561662,
    phi_oneHundredTwentySixDT_148965627396955625866431561663, phi_oneHundredTwentySixDT_148965627396955625866431561664, phi_oneHundredTwentySixDT_148965627396955625866431561665,
    phi_oneHundredTwentySixDT_148965627396955625866431561666, phi_oneHundredTwentySixDT_148965627396955625866431561667, phi_oneHundredTwentySixDT_148965627396955625866431561668,
    phi_oneHundredTwentySixDT_148965627396955625866431561669, phi_oneHundredTwentySixDT_148965627396955625866431561670, phi_oneHundredTwentySixDT_148965627396955625866431561671,
    phi_oneHundredTwentySixDT_148965627396955625866431561672, phi_oneHundredTwentySixDT_148965627396955625866431561673, phi_oneHundredTwentySixDT_148965627396955625866431561674,
    phi_oneHundredTwentySixDT_148965627396955625866431561675, phi_oneHundredTwentySixDT_148965627396955625866431561676, phi_oneHundredTwentySixDT_148965627396955625866431561677,
    phi_oneHundredTwentySixDT_148965627396955625866431561678, phi_oneHundredTwentySixDT_148965627396955625866431561679, phi_oneHundredTwentySixDT_148965627396955625866431561680,
    phi_oneHundredTwentySixDT_148965627396955625866431561681, phi_oneHundredTwentySixDT_148965627396955625866431561682, phi_oneHundredTwentySixDT_148965627396955625866431561683,
    phi_oneHundredTwentySixDT_148965627396955625866431561684, phi_oneHundredTwentySixDT_148965627396955625866431561685, phi_oneHundredTwentySixDT_148965627396955625866431561686,
    phi_oneHundredTwentySixDT_148965627396955625866431561687, phi_oneHundredTwentySixDT_148965627396955625866431561688, phi_oneHundredTwentySixDT_148965627396955625866431561689,
    phi_oneHundredTwentySixDT_148965627396955625866431561690, phi_oneHundredTwentySixDT_148965627396955625866431561691, phi_oneHundredTwentySixDT_148965627396955625866431561692,
    phi_oneHundredTwentySixDT_148965627396955625866431561693, phi_oneHundredTwentySixDT_148965627396955625866431561694, phi_oneHundredTwentySixDT_148965627396955625866431561695,
    phi_oneHundredTwentySixDT_148965627396955625866431561696, phi_oneHundredTwentySixDT_148965627396955625866431561697, phi_oneHundredTwentySixDT_148965627396955625866431561698,
    phi_oneHundredTwentySixDT_148965627396955625866431561699, phi_oneHundredTwentySixDT_148965627396955625866431561700, phi_oneHundredTwentySixDT_148965627396955625866431561701
    ]

end TotientTailPeriodKiller
end Erdos249257
